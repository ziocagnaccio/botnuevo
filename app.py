"""
TREND BOT B — Hyperliquid (BTC / ETH) — risk-based rules
NO TRADINGVIEW: the bot downloads Hyperliquid candles and calculates the
       indicators itself. UptimeRobot opens /manage every 5 minutes: that
       checks trades AND runs the strategy when a new 3h candle has closed.
       Telegram messages are sent directly by this app.

ENTRY (all must be true, checked when a 3h candle closes):
  1. Trend   LONG: close > EMA100 and EMA20 > EMA50   SHORT: the opposite
  2. ADX(14) > 20
  3. At least 2 of 3: MACD cross in the last 2 candles / RSI in range / volume > 20-candle avg
  4. Candle range <= 2.5 x ATR(14)
  5. Funding not against the trade by more than 0.005% per hour
  6. No cooldown or portfolio limit blocks it

EXITS:
  Stop-loss = 2 x ATR, kept between 1.5% and 5%.  R = stop-loss distance.
  TP1 at +1.5R: close 50%, move stop-loss to entry.
  Rest: close if price moves 2 x ATR against the best price, or a 3h candle
        closes back across EMA20.
  Opposite signal while open: close, don't flip, apply stop-loss cooldown.

SIZE:  risk 1% of equity per trade (0.5% after 3 losses in a row, until a win).
       position = risk $ / stop-loss %, max 1.5 x equity, 5x isolated.
LIMITS: total open risk max 2%; same direction max 2 positions / 1.5% risk.
COOLDOWN: after a loss, 6 hours AND price at least 1 x ATR from the exit.
SAFETY: every cycle, compares its records with the exchange. On a mismatch it
        stops trading and alerts you (restart with /resume after checking).
NO circuit breakers (removed on purpose).
"""
import os
import json
import math
import time
import threading
from datetime import datetime, timezone

import requests
from flask import Flask, jsonify
from eth_account import Account
from hyperliquid.info import Info
from hyperliquid.exchange import Exchange
from hyperliquid.utils import constants

app = Flask(__name__)

# ========================= CONFIG — the rules =========================
COINS                   = ["BTC", "ETH"]
LEVERAGE                = 5          # isolated
RISK_PCT                = 0.01       # 1% of equity per trade
RISK_PCT_AFTER_STREAK   = 0.005      # 0.5% after 3 losses in a row
LOSS_STREAK_LIMIT       = 3

SL_ATR_MULT             = 2.0        # stop-loss = 2 x ATR
SL_MIN_PCT              = 0.015      # ...but at least 1.5%
SL_MAX_PCT              = 0.05       # ...and at most 5%
TP1_R                   = 1.5        # first take-profit at +1.5R
TP1_FRACTION            = 0.5        # close 50% there
TRAIL_ATR_MULT          = 2.0        # rest: exit 2 x ATR from the best price

ADX_MIN                 = 20
RSI_LONG                = (50, 70)
RSI_SHORT               = (30, 50)
VOL_MIN_RATIO           = 1.0        # volume above the 20-candle average
RANGE_ATR_MAX           = 2.5        # skip huge candles
FUNDING_MAX_AGAINST     = 0.00005    # 0.005% per hour

MAX_TOTAL_RISK          = 0.02       # all open trades together
MAX_SAME_DIR_RISK       = 0.015      # same direction together
MAX_SAME_DIR_POSITIONS  = 2
MAX_NOTIONAL_X_EQUITY   = 1.5        # position never bigger than 1.5 x equity

COOLDOWN_HOURS          = 6          # 2 candles of 3h
REENTRY_ATR_MULT        = 1.0

MIN_ORDER_USD           = 12.0       # Hyperliquid minimum is ~$10
SLIPPAGE                = 0.01
STATE_FILE              = "state_bot_b.json"
# =====================================================================

WALLET_KEY = os.environ["HL_PRIVATE_KEY"]
MAIN_ADDR  = os.environ["HL_WALLET_ADDR"]
# TELEGRAM_TOKEN and TELEGRAM_CHAT_ID can hold several values separated by commas.
# They are matched in order: 1st token -> 1st chat ID, 2nd token -> 2nd chat ID.
# With only one token, that token is used for every chat ID.
TG_TOKENS  = [t.strip() for t in os.environ.get("TELEGRAM_TOKEN", "").split(",") if t.strip()]
TG_CHATS   = [c.strip() for c in os.environ.get("TELEGRAM_CHAT_ID", "").split(",") if c.strip()]

_wallet  = Account.from_key(WALLET_KEY)
info     = Info(constants.MAINNET_API_URL, skip_ws=True)
exchange = Exchange(_wallet, constants.MAINNET_API_URL, account_address=MAIN_ADDR)

LOCK = threading.Lock()
_sz_dec_cache = {}


def now_ms():
    return int(time.time() * 1000)


def default_state():
    return {"trades": {}, "loss_streak": 0, "cooldowns": {}, "halted": False,
            "halt_reason": "", "history": []}


state = default_state()

# --------------------------- telegram ---------------------------

def tg(text):
    print("[TG]", text)
    if not TG_TOKENS or not TG_CHATS:
        return
    for n, chat in enumerate(TG_CHATS):
        token = TG_TOKENS[0] if len(TG_TOKENS) == 1 else (TG_TOKENS[n] if n < len(TG_TOKENS) else None)
        if not token:
            print(f"[TG] no token for chat {chat}")
            continue
        try:
            requests.post(f"https://api.telegram.org/bot{token}/sendMessage",
                          json={"chat_id": chat, "text": "🅱️ BOT B\n" + text}, timeout=10)
        except Exception as e:
            print(f"[TG] failed: {e}")

# ===================== CANDLES + INDICATORS (no TradingView) =====================
# Hyperliquid has no 3h candles, so we download 1h candles and join them 3 by 3
# (00-03, 03-06, ... UTC). Formulas are the same as TradingView's.
HOUR_MS        = 3600 * 1000
CANDLE_MS      = 3 * HOUR_MS
HISTORY_DAYS   = 60           # enough history for EMA100 / ADX to settle
FRESH_MINUTES  = 20           # only act on a candle that closed in the last 20 min
_last_candle   = {}           # coin -> open time of the last 3h candle already checked


def fetch_3h_candles(coin):
    end = int(time.time() * 1000)
    start = end - HISTORY_DAYS * 24 * HOUR_MS
    raw = info.candles_snapshot(coin, "1h", start, end)
    groups = {}
    for c in raw:
        t = int(c["t"])
        groups.setdefault(t - (t % CANDLE_MS), []).append(c)
    out = []
    for g in sorted(groups):
        if g + CANDLE_MS > end - 30000:        # this 3h candle hasn't closed yet
            continue
        cs = sorted(groups[g], key=lambda c: int(c["t"]))
        out.append({"t": g,
                    "o": float(cs[0]["o"]), "c": float(cs[-1]["c"]),
                    "h": max(float(c["h"]) for c in cs), "l": min(float(c["l"]) for c in cs),
                    "v": sum(float(c["v"]) for c in cs)})
    return out


def _smooth(src, n, alpha):
    """EMA / RMA like TradingView: starts with a simple average of the first n values."""
    out, prev, buf = [None] * len(src), None, []
    for i, x in enumerate(src):
        if x is None:
            continue
        if prev is None:
            buf.append(x)
            if len(buf) == n:
                prev = sum(buf) / n
                out[i] = prev
        else:
            prev = alpha * x + (1 - alpha) * prev
            out[i] = prev
    return out


def ind_ema(src, n):
    return _smooth(src, n, 2.0 / (n + 1))


def ind_rma(src, n):
    return _smooth(src, n, 1.0 / n)


def ind_sma(src, n):
    out = [None] * len(src)
    for i in range(n - 1, len(src)):
        w = src[i - n + 1:i + 1]
        if None not in w:
            out[i] = sum(w) / n
    return out


def compute_signal(coin):
    """Builds the same data TradingView used to send, from Hyperliquid candles."""
    k = fetch_3h_candles(coin)
    if len(k) < 150:
        raise ValueError(f"not enough candles ({len(k)})")
    o = [x["o"] for x in k]; h = [x["h"] for x in k]; l = [x["l"] for x in k]
    c = [x["c"] for x in k]; v = [x["v"] for x in k]
    n = len(c)

    ema20, ema50, ema100 = ind_ema(c, 20), ind_ema(c, 50), ind_ema(c, 100)

    # RSI 14
    ups = [None] + [max(c[i] - c[i - 1], 0.0) for i in range(1, n)]
    dns = [None] + [max(c[i - 1] - c[i], 0.0) for i in range(1, n)]
    ru, rd = ind_rma(ups, 14), ind_rma(dns, 14)
    rsi = 100.0 if rd[-1] == 0 else (0.0 if ru[-1] == 0 else 100 - 100 / (1 + ru[-1] / rd[-1]))

    # MACD 12 26 9
    e12, e26 = ind_ema(c, 12), ind_ema(c, 26)
    macd = [a - b if a is not None and b is not None else None for a, b in zip(e12, e26)]
    sig = ind_ema(macd, 9)
    hist = macd[-1] - sig[-1]

    def cross_up(i):
        return macd[i] > sig[i] and macd[i - 1] <= sig[i - 1]

    def cross_dn(i):
        return macd[i] < sig[i] and macd[i - 1] >= sig[i - 1]

    # ATR 14 + ADX 14
    tr = [h[0] - l[0]] + [max(h[i] - l[i], abs(h[i] - c[i - 1]), abs(l[i] - c[i - 1])) for i in range(1, n)]
    atr = ind_rma(tr, 14)
    pdm, mdm = [None], [None]
    for i in range(1, n):
        up, dn = h[i] - h[i - 1], l[i - 1] - l[i]
        pdm.append(up if (up > dn and up > 0) else 0.0)
        mdm.append(dn if (dn > up and dn > 0) else 0.0)
    trr = ind_rma([None] + tr[1:], 14)
    pr, mr = ind_rma(pdm, 14), ind_rma(mdm, 14)
    dx = []
    for i in range(n):
        if trr[i] is None or pr[i] is None or mr[i] is None or trr[i] == 0:
            dx.append(None)
            continue
        p, m = 100 * pr[i] / trr[i], 100 * mr[i] / trr[i]
        s = p + m
        dx.append(abs(p - m) / (s if s != 0 else 1))
    adx = 100 * ind_rma(dx, 14)[-1]

    vavg = ind_sma(v, 20)[-1]
    return {
        "symbol": coin, "candle_time": k[-1]["t"],
        "price": c[-1], "high": h[-1], "low": l[-1],
        "ema20": ema20[-1], "ema50": ema50[-1], "ema100": ema100[-1],
        "rsi": rsi, "macd_hist": hist,
        "macd_up2": cross_up(n - 1) or cross_up(n - 2),
        "macd_dn2": cross_dn(n - 1) or cross_dn(n - 2),
        "adx": adx, "atr": atr[-1], "atr_pct": atr[-1] / c[-1] * 100,
        "vol_ratio": (v[-1] / vavg) if vavg else 0.0,
    }


def candle_clock(handler):
    """Called every 5 min: if a new 3h candle closed, run the strategy on it."""
    results = {}
    now = int(time.time() * 1000)
    for coin in COINS:
        try:
            s = compute_signal(coin)
        except Exception as e:
            results[coin] = f"candle error: {e}"
            continue
        ct = s["candle_time"]
        if _last_candle.get(coin) is not None and ct <= _last_candle[coin]:
            results[coin] = "waiting for the next 3h candle"
            continue
        _last_candle[coin] = ct
        if now - (ct + CANDLE_MS) > FRESH_MINUTES * 60 * 1000:
            results[coin] = "candle too old, waiting for the next one"
            continue
        try:
            results[coin] = handler(s)
        except Exception as e:
            results[coin] = f"error: {e}"
    return results
# ================================================================================

# --------------------------- state ---------------------------

def save_state():
    try:
        tmp = STATE_FILE + ".tmp"
        with open(tmp, "w") as fh:
            json.dump(state, fh)
        os.replace(tmp, STATE_FILE)
    except Exception as e:
        print(f"[state] save failed: {e}")

# --------------------------- exchange helpers ---------------------------

def sz_decimals(coin):
    if coin not in _sz_dec_cache:
        for a in info.meta()["universe"]:
            _sz_dec_cache[a["name"]] = int(a["szDecimals"])
    return _sz_dec_cache.get(coin, 2)


def floor_sz(coin, x):
    f = 10 ** sz_decimals(coin)
    return math.floor(x * f) / f


def round_sz(coin, x):
    return round(x, sz_decimals(coin))


def round_px(coin, px):
    if px <= 0:
        return px
    sig = 5 - int(math.floor(math.log10(abs(px)))) - 1
    max_dec = 6 - sz_decimals(coin)
    return round(px, max(0, min(sig, max_dec)))


def order_ok(res):
    try:
        if res.get("status") != "ok":
            return False
        statuses = res["response"]["data"]["statuses"]
        return all(isinstance(s, dict) and "error" not in s for s in statuses)
    except Exception:
        return False


def account():
    """equity, free money, {coin: (szi, entryPx)}"""
    s = info.user_state(MAIN_ADDR)
    equity = float(s["marginSummary"]["accountValue"])
    free = float(s.get("withdrawable", equity) or equity)
    pos = {}
    for p in s.get("assetPositions", []):
        q = p.get("position", {})
        szi = float(q.get("szi", 0) or 0)
        if szi != 0:
            pos[q.get("coin")] = (szi, float(q.get("entryPx", 0) or 0))
    return equity, free, pos


def trigger_orders():
    """All open trigger (TP/SL) orders, grouped by coin."""
    out = {}
    try:
        orders = info.frontend_open_orders(MAIN_ADDR)
    except Exception as e:
        print(f"[orders] {e}")
        orders = []
    for o in orders:
        tpx = float(o.get("triggerPx", 0) or 0)
        if o.get("isTrigger") or tpx > 0:
            out.setdefault(o.get("coin"), []).append(o)
    return out


def stop_orders(side, entry, orders):
    """Trigger orders on the losing side of entry (or at entry) = stop-losses."""
    res = []
    for o in orders:
        tpx = float(o.get("triggerPx", 0) or 0)
        if tpx <= 0:
            continue
        if (side == "LONG" and tpx <= entry * 1.0005) or (side == "SHORT" and tpx >= entry * 0.9995):
            res.append(o)
    return res


def profit_orders(side, entry, orders):
    res = []
    for o in orders:
        tpx = float(o.get("triggerPx", 0) or 0)
        if tpx <= 0:
            continue
        if (side == "LONG" and tpx > entry * 1.0005) or (side == "SHORT" and tpx < entry * 0.9995):
            res.append(o)
    return res


def cancel_coin_orders(coin):
    try:
        for o in info.open_orders(MAIN_ADDR):
            if o.get("coin") == coin:
                exchange.cancel(coin, o["oid"])
    except Exception as e:
        print(f"[cancel] {coin}: {e}")


def place_trigger(coin, side, size, px, kind):
    """kind = 'sl' or 'tp'. Reduce-only market trigger that closes (part of) a position."""
    is_buy = side == "SHORT"          # closing a short = buy
    return exchange.order(coin, is_buy, size, px,
                          {"trigger": {"triggerPx": px, "isMarket": True, "tpsl": kind}},
                          reduce_only=True)


def close_now(coin, sz=None):
    try:
        res = exchange.market_close(coin, sz) if sz else exchange.market_close(coin)
        print(f"[close] {coin} sz={sz}: {res}")
        return res
    except Exception as e:
        tg(f"❗ {coin}: market close FAILED: {e}\nCheck Hyperliquid now.")
        return None


def funding_rate(coin):
    meta, ctxs = info.meta_and_asset_ctxs()
    for a, c in zip(meta["universe"], ctxs):
        if a["name"] == coin:
            return float(c.get("funding", 0) or 0)
    return 0.0


def wait_for_fill(coin, side, tries=12, pause=0.5):
    for _ in range(tries):
        time.sleep(pause)
        _, _, pos = account()
        if coin in pos:
            szi, entry = pos[coin]
            if (szi > 0) == (side == "LONG"):
                return abs(szi), entry
    return 0.0, 0.0


def pnl_since(coin, since_ms):
    """Net result (closed PnL minus fees) of fills since since_ms, and last price."""
    pnl, last_px = 0.0, None
    try:
        fills = sorted(info.user_fills(MAIN_ADDR), key=lambda f: f["time"])
    except Exception as e:
        print(f"[fills] {e}")
        return 0.0, None
    for f in fills:
        if f.get("coin") != coin or int(f["time"]) < since_ms:
            continue
        pnl += float(f.get("closedPnl", 0) or 0) - float(f.get("fee", 0) or 0)
        last_px = float(f["px"])
    return pnl, last_px

# --------------------------- bookkeeping ---------------------------

def halt(reason):
    state["halted"] = True
    state["halt_reason"] = reason
    save_state()
    tg(f"🛑 TRADING STOPPED\n{reason}\n\nCheck Hyperliquid. When everything is OK, open /resume to restart.")


def record_close(coin, reason, force_cooldown=False):
    t = state["trades"].pop(coin, None)
    if not t:
        return
    time.sleep(1.5)                        # let the fills register
    cancel_coin_orders(coin)               # remove leftover TP/SL
    pnl, exit_px = pnl_since(coin, t["opened_at"])
    if exit_px is None:
        try:
            exit_px = float(info.all_mids().get(coin, 0) or 0)
        except Exception:
            exit_px = t["entry"]

    if pnl < 0:
        state["loss_streak"] += 1
    elif pnl > 0:
        state["loss_streak"] = 0

    if pnl < 0 or force_cooldown:
        state["cooldowns"][coin] = {"until": time.time() + COOLDOWN_HOURS * 3600, "exit_px": exit_px}

    state["history"] = (state["history"] + [{
        "coin": coin, "side": t["side"], "entry": t["entry"], "exit": exit_px,
        "pnl": round(pnl, 2), "reason": reason, "time": datetime.now(timezone.utc).isoformat()
    }])[-30:]
    save_state()

    icon = "✅" if pnl > 0 else ("❌" if pnl < 0 else "➖")
    extra = ""
    if state["loss_streak"] >= LOSS_STREAK_LIMIT:
        extra = f"\n⚠️ {state['loss_streak']} losses in a row: risk now 0.5% until the next win."
    tg(f"{icon} {coin} {t['side']} CLOSED ({reason})\n"
       f"Entry {t['entry']} → Exit {exit_px}\nResult: ${pnl:.2f}{extra}")


def on_tp1(coin, t, remaining):
    """TP1 filled: cancel old orders, stop-loss to entry for the rest."""
    cancel_coin_orders(coin)
    sl_px = round_px(coin, t["entry"])
    ok = False
    try:
        ok = order_ok(place_trigger(coin, t["side"], remaining, sl_px, "sl"))
    except Exception as e:
        print(f"[tp1] {e}")
    if not ok:
        close_now(coin)
        record_close(coin, "stop-loss could not be moved to entry → closed for safety")
        tg(f"❗ {coin}: could not place the stop-loss at entry, position closed at market.")
        return
    try:
        mark = float(info.all_mids().get(coin, t["entry"]) or t["entry"])
    except Exception:
        mark = t["entry"]
    t.update({"tp1_done": True, "risk_usd": 0.0, "sl_px": sl_px, "size_after_tp1": remaining,
              "best": mark})
    save_state()
    tg(f"💰 {coin} {t['side']}: TP1 hit, 50% closed in profit.\n"
       f"Stop-loss moved to entry ({sl_px}). The rest can't lose anymore.")


def same(a, b, coin):
    step = 10 ** -sz_decimals(coin)
    return abs(a - b) <= max(step * 1.5, 0.02 * max(a, b))


def sync():
    """Compare records with the exchange. Detect closes / TP1 / mismatches."""
    equity, free, pos = account()
    orders = trigger_orders()
    for coin in COINS:
        p = pos.get(coin)
        t = state["trades"].get(coin)

        if t and not p:
            record_close(coin, "stop-loss / take-profit on exchange")
            continue
        if p and not t:
            halt(f"{coin}: there is a position on Hyperliquid that Bot B did not open.")
            continue
        if not p:
            continue

        szi, _ = p
        side = "LONG" if szi > 0 else "SHORT"
        size = abs(szi)
        if side != t["side"]:
            halt(f"{coin}: Bot B thinks it is {t['side']}, Hyperliquid shows {side}.")
            continue

        if not t["tp1_done"]:
            if not same(size, t["initial_size"], coin):
                if same(size, t["size_after_tp1"], coin):
                    on_tp1(coin, t, size)
                    continue
                halt(f"{coin}: size on Hyperliquid ({size}) doesn't match Bot B ({t['initial_size']}).")
                continue
        elif not same(size, t["size_after_tp1"], coin):
            halt(f"{coin}: size on Hyperliquid ({size}) doesn't match Bot B ({t['size_after_tp1']}).")
            continue

        if not stop_orders(side, t["entry"], orders.get(coin, [])):
            close_now(coin)
            record_close(coin, "no stop-loss found → closed for safety")
            halt(f"{coin}: position had NO stop-loss on Hyperliquid. Closed it at market.")
    return equity, free


def rebuild_from_exchange():
    """Used only when the state file is missing (after a redeploy/restart)."""
    global state
    state = default_state()
    try:
        fills = sorted(info.user_fills(MAIN_ADDR), key=lambda f: f["time"])
    except Exception as e:
        print(f"[rebuild] fills: {e}")
        fills = []

    # finished trades from fills -> loss streak + cooldowns
    acc, opened, results = {}, {}, []
    for f in fills:
        coin = f.get("coin")
        start = float(f.get("startPosition", 0) or 0)
        sz = float(f.get("sz", 0) or 0)
        new = start + sz if f.get("side") == "B" else start - sz
        if abs(start) < 1e-12:
            acc[coin] = 0.0
            opened[coin] = int(f["time"])
        acc[coin] = acc.get(coin, 0.0) + float(f.get("closedPnl", 0) or 0) - float(f.get("fee", 0) or 0)
        if abs(new) < 1e-12 and abs(start) > 0:
            results.append({"coin": coin, "time": int(f["time"]), "pnl": acc[coin], "px": float(f["px"])})
            acc[coin] = 0.0
    streak = 0
    for r in reversed(results):
        if r["pnl"] < 0:
            streak += 1
        elif r["pnl"] > 0:
            break
    state["loss_streak"] = streak
    for coin in COINS:
        last = [r for r in results if r["coin"] == coin]
        if last and last[-1]["pnl"] < 0:
            until = last[-1]["time"] / 1000 + COOLDOWN_HOURS * 3600
            if until > time.time():
                state["cooldowns"][coin] = {"until": until, "exit_px": last[-1]["px"]}

    # open positions -> adopt them if they have a stop-loss
    try:
        _, _, pos = account()
        orders = trigger_orders()
        for coin, (szi, entry) in pos.items():
            if coin not in COINS:
                continue
            side = "LONG" if szi > 0 else "SHORT"
            size = abs(szi)
            stops = stop_orders(side, entry, orders.get(coin, []))
            if not stops:
                continue                   # sync() will halt and alert
            sl_px = float(stops[0]["triggerPx"])
            tp1_done = abs(sl_px - entry) / entry < 0.001
            if tp1_done:
                sl_pct, initial, after = SL_MIN_PCT, size * 2, size
            else:
                sl_pct = abs(entry - sl_px) / entry
                initial = size
                after = round_sz(coin, size - floor_sz(coin, size * TP1_FRACTION))
            tps = profit_orders(side, entry, orders.get(coin, []))
            tp1_px = float(tps[0]["triggerPx"]) if tps else round_px(
                coin, entry * (1 + TP1_R * sl_pct) if side == "LONG" else entry * (1 - TP1_R * sl_pct))
            state["trades"][coin] = {
                "side": side, "entry": entry, "initial_size": initial, "size_after_tp1": after,
                "sl_pct": sl_pct, "sl_px": sl_px, "tp1_px": tp1_px, "tp1_done": tp1_done,
                "risk_usd": 0.0 if tp1_done else size * entry * sl_pct,
                "best": entry, "atr": entry * sl_pct / SL_ATR_MULT,
                "opened_at": opened.get(coin, now_ms() - 86400000),
            }
    except Exception as e:
        print(f"[rebuild] positions: {e}")
    save_state()
    print("[rebuild] state rebuilt from Hyperliquid")


def load_state():
    global state
    try:
        with open(STATE_FILE) as fh:
            state = {**default_state(), **json.load(fh)}
            return
    except Exception:
        pass
    rebuild_from_exchange()

# --------------------------- the rules ---------------------------

def evaluate(s):
    """Entry rules 1-4. Returns (side or None, explanation)."""
    c = s["price"]
    if c > s["ema100"] and s["ema20"] > s["ema50"]:
        side = "LONG"
    elif c < s["ema100"] and s["ema20"] < s["ema50"]:
        side = "SHORT"
    else:
        return None, "no clear trend"
    if s["adx"] <= ADX_MIN:
        return None, f"ADX {s['adx']:.1f} not above {ADX_MIN}"
    if side == "LONG":
        votes = [s["macd_up2"], RSI_LONG[0] <= s["rsi"] <= RSI_LONG[1], s["vol_ratio"] > VOL_MIN_RATIO]
    else:
        votes = [s["macd_dn2"], RSI_SHORT[0] <= s["rsi"] <= RSI_SHORT[1], s["vol_ratio"] > VOL_MIN_RATIO]
    if sum(votes) < 2:
        return None, f"{side} trend but only {sum(votes)}/3 confirmations"
    if (s["high"] - s["low"]) > RANGE_ATR_MAX * s["atr"]:
        return None, "candle too big (more than 2.5 x ATR)"
    return side, f"{side}: {sum(votes)}/3 confirmations, ADX {s['adx']:.1f}"


def risk_allowed(side, equity):
    base = RISK_PCT_AFTER_STREAK if state["loss_streak"] >= LOSS_STREAK_LIMIT else RISK_PCT
    trades = state["trades"].values()
    total = sum(t["risk_usd"] for t in trades)
    same_dir = [t for t in trades if t["side"] == side]
    if len(same_dir) >= MAX_SAME_DIR_POSITIONS:
        return 0.0, "already 2 positions in this direction"
    allowed = min(base * equity, MAX_TOTAL_RISK * equity - total)
    if same_dir:
        allowed = min(allowed, MAX_SAME_DIR_RISK * equity - sum(t["risk_usd"] for t in same_dir))
    if allowed <= 0:
        return 0.0, "portfolio risk limit reached"
    return allowed, f"risk ${allowed:.2f} ({allowed / equity * 100:.2f}% of equity)"


def sl_distance(price, atr):
    return min(max(SL_ATR_MULT * atr / price, SL_MIN_PCT), SL_MAX_PCT)


def to_bool(x):
    if isinstance(x, bool):
        return x
    return str(x).strip().lower() in ("true", "1", "yes")

# --------------------------- routes ---------------------------

def handle_signal(coin, s):
    if state["halted"]:
        return {"status": "halted", "reason": state["halt_reason"]}
    equity, free = sync()
    if state["halted"]:
        return {"status": "halted", "reason": state["halt_reason"]}

    price = s["price"]
    side, why = evaluate(s)

    # ---- a trade is already open on this coin ----
    t = state["trades"].get(coin)
    if t:
        t["atr"] = s["atr"]
        save_state()
        if t["tp1_done"] and ((t["side"] == "LONG" and price < s["ema20"]) or
                              (t["side"] == "SHORT" and price > s["ema20"])):
            close_now(coin)
            record_close(coin, "3h candle closed back across EMA20")
            return {"status": "closed", "coin": coin, "reason": "EMA20 exit"}
        if side and side != t["side"]:
            close_now(coin)
            record_close(coin, "opposite signal", force_cooldown=True)
            return {"status": "closed", "coin": coin, "reason": "opposite signal, not flipping"}
        return {"status": "skipped", "coin": coin, "reason": f"already {t['side']}"}

    if not side:
        return {"status": "no_trade", "coin": coin, "reason": why}

    # ---- rule 5: funding ----
    fr = funding_rate(coin)
    if (side == "LONG" and fr > FUNDING_MAX_AGAINST) or (side == "SHORT" and fr < -FUNDING_MAX_AGAINST):
        return {"status": "skipped", "coin": coin, "reason": f"funding against the trade ({fr * 100:.4f}%/h)"}

    # ---- rule 6a: cooldown ----
    cd = state["cooldowns"].get(coin)
    if cd:
        if time.time() < cd["until"]:
            left = (cd["until"] - time.time()) / 3600
            return {"status": "skipped", "coin": coin, "reason": f"cooldown ({left:.1f}h left)"}
        if abs(price - cd["exit_px"]) < REENTRY_ATR_MULT * s["atr"]:
            return {"status": "skipped", "coin": coin, "reason": "price not 1 ATR away from last exit"}
        state["cooldowns"].pop(coin, None)
        save_state()

    # ---- rule 6b: portfolio limits + size ----
    risk_usd, risk_why = risk_allowed(side, equity)
    if risk_usd <= 0:
        return {"status": "skipped", "coin": coin, "reason": risk_why}
    sl_pct = sl_distance(price, s["atr"])
    notional = risk_usd / sl_pct
    notional = min(notional, MAX_NOTIONAL_X_EQUITY * equity, free * LEVERAGE * 0.9)
    size = floor_sz(coin, notional / price)
    if size * price < MIN_ORDER_USD or floor_sz(coin, size * TP1_FRACTION) * price < MIN_ORDER_USD / 2:
        return {"status": "skipped", "coin": coin, "reason": f"position too small (${size * price:.2f})"}

    # ---- open ----
    t0 = now_ms() - 5000
    cancel_coin_orders(coin)
    exchange.update_leverage(LEVERAGE, coin, is_cross=False)
    res = exchange.market_open(coin, side == "LONG", size, None, SLIPPAGE)
    filled, entry = wait_for_fill(coin, side)
    if filled <= 0:
        tg(f"❗ {coin} {side}: entry order not confirmed.\n{res}")
        return {"status": "error", "coin": coin, "reason": "entry not confirmed"}

    if side == "LONG":
        sl_px = round_px(coin, entry * (1 - sl_pct))
        tp1_px = round_px(coin, entry * (1 + TP1_R * sl_pct))
    else:
        sl_px = round_px(coin, entry * (1 + sl_pct))
        tp1_px = round_px(coin, entry * (1 - TP1_R * sl_pct))

    # stop-loss first — if it fails, close immediately
    sl_ok = False
    try:
        sl_ok = order_ok(place_trigger(coin, side, filled, sl_px, "sl"))
    except Exception as e:
        print(f"[sl] {e}")
    if not sl_ok:
        close_now(coin)
        tg(f"❗ {coin} {side}: stop-loss could NOT be placed. Position closed at market.")
        return {"status": "error", "coin": coin, "reason": "stop-loss failed, closed"}

    half = floor_sz(coin, filled * TP1_FRACTION)
    remaining = round_sz(coin, filled - half)
    tp_ok = False
    try:
        tp_ok = order_ok(place_trigger(coin, side, half, tp1_px, "tp"))
    except Exception as e:
        print(f"[tp1] {e}")
    if not tp_ok:
        tg(f"⚠️ {coin}: TP1 order failed to place. The bot will take TP1 itself when price gets there.")

    risk_real = filled * entry * sl_pct
    state["trades"][coin] = {
        "side": side, "entry": entry, "initial_size": filled, "size_after_tp1": remaining,
        "sl_pct": sl_pct, "sl_px": sl_px, "tp1_px": tp1_px, "tp1_done": False,
        "risk_usd": risk_real, "best": entry, "atr": s["atr"], "opened_at": t0,
    }
    save_state()
    tg(f"🚀 {coin} {side} opened @ {entry}\n"
       f"Size ${filled * entry:.0f} ({LEVERAGE}x isolated, collateral ~${filled * entry / LEVERAGE:.0f})\n"
       f"Stop-loss {sl_px} (−{sl_pct * 100:.2f}%) → max loss ~${risk_real:.2f}\n"
       f"TP1 {tp1_px} (+{TP1_R * sl_pct * 100:.2f}%, closes 50%)\n{why}")
    return {"status": "executed", "coin": coin, "side": side, "entry_price": entry,
            "size": filled, "sl": sl_px, "tp1": tp1_px, "risk_usd": round(risk_real, 2)}


@app.route("/manage", methods=["GET"])
def manage():
    """Called every 5 minutes by UptimeRobot: sync, backup TP1, trailing exit."""
    with LOCK:
        actions = []
        try:
            if state["halted"]:
                return jsonify({"status": "halted", "reason": state["halt_reason"]}), 200
            sync()
            if state["halted"]:
                return jsonify({"status": "halted", "reason": state["halt_reason"]}), 200
            mids = info.all_mids()
            orders = trigger_orders()
            for coin, t in list(state["trades"].items()):
                mark = float(mids.get(coin, 0) or 0)
                if mark <= 0:
                    continue
                long_ = t["side"] == "LONG"
                if not t["tp1_done"]:
                    hit = mark >= t["tp1_px"] if long_ else mark <= t["tp1_px"]
                    tp_on_exchange = profit_orders(t["side"], t["entry"], orders.get(coin, []))
                    if hit and not tp_on_exchange:      # backup only if the TP1 order is missing
                        close_now(coin, round_sz(coin, t["initial_size"] - t["size_after_tp1"]))
                        time.sleep(2)
                        _, _, pos = account()
                        if coin in pos:
                            on_tp1(coin, t, abs(pos[coin][0]))
                        else:
                            record_close(coin, "take-profit")
                        actions.append(f"{coin} backup TP1")
                    continue
                t["best"] = max(t["best"], mark) if long_ else min(t["best"], mark)
                dist = TRAIL_ATR_MULT * t["atr"]
                if (long_ and mark <= t["best"] - dist) or (not long_ and mark >= t["best"] + dist):
                    close_now(coin)
                    record_close(coin, "trailing exit (2 x ATR from the best price)")
                    actions.append(f"{coin} trailing exit")
            save_state()
        except Exception as e:
            actions.append(f"error: {e}")
        def run_signal(s):
            try:
                return handle_signal(s["symbol"], s)
            except Exception as e:
                tg(f"❗ {s['symbol']}: error while handling the 3h candle: {e}")
                return {"status": "error", "reason": str(e)}
        results = candle_clock(run_signal)
        state["last_checks"] = {c: {"result": r, "checked": datetime.now(timezone.utc).isoformat()}
                                for c, r in results.items()}
        save_state()
        return jsonify({"status": "managed", "actions": actions, "candles": results}), 200


@app.route("/signals", methods=["GET"])
def signals():
    """See what the bot calculates right now (no trading)."""
    out = {}
    for coin in COINS:
        try:
            s = compute_signal(coin)
            side, why = evaluate(s)
            s["candle_time"] = datetime.fromtimestamp(s["candle_time"] / 1000, timezone.utc).strftime("%Y-%m-%d %H:%M UTC")
            out[coin] = {"decision": side or "NOTHING", "why": why,
                         **{k: (round(v, 4) if isinstance(v, float) else v) for k, v in s.items()}}
        except Exception as e:
            out[coin] = {"error": str(e)}
    return jsonify(out)


@app.route("/status", methods=["GET"])
def status():
    try:
        equity, free, pos = account()
        risk = RISK_PCT_AFTER_STREAK if state["loss_streak"] >= LOSS_STREAK_LIMIT else RISK_PCT
        return jsonify({
            "status": "HALTED" if state["halted"] else "running", "bot": "B (new rules, no TradingView)",
            "halt_reason": state["halt_reason"], "coins": COINS,
            "leverage": f"{LEVERAGE}x isolated", "account_equity": round(equity, 2),
            "risk_per_trade_now": f"{risk * 100}%", "loss_streak": state["loss_streak"],
            "open_positions_exchange": pos, "trades_bot": state["trades"],
            "cooldowns": {c: {"hours_left": round(max(0, v["until"] - time.time()) / 3600, 2),
                              "exit_px": v["exit_px"]} for c, v in state["cooldowns"].items()},
            "last_results": state["history"][-10:],
            "last_checks": state.get("last_checks", {}),
        })
    except Exception as e:
        return jsonify({"status": "error", "reason": str(e)}), 200


@app.route("/resume", methods=["GET"])
def resume():
    with LOCK:
        was = state["halt_reason"]
        rebuild_from_exchange()            # re-read everything from Hyperliquid
        state["halted"] = False
        state["halt_reason"] = ""
        save_state()
    tg(f"▶️ Trading restarted (was stopped for: {was or 'nothing'}).")
    return jsonify({"status": "resumed"}), 200


@app.route("/test", methods=["GET"])
def test_telegram():
    """Sends a test message to Telegram, and shows which wallet this bot uses."""
    try:
        equity = float(info.user_state(MAIN_ADDR)["marginSummary"]["accountValue"])
    except Exception:
        equity = -1
    tg(f"👋 Test message. I'm Bot B (new rules).\n"
       f"Wallet: {MAIN_ADDR[:6]}...{MAIN_ADDR[-4:]}\nBalance: ${equity:.2f}")
    return jsonify({"status": "test sent", "wallet": MAIN_ADDR, "equity": round(equity, 2)})


@app.route("/", methods=["GET"])
def home():
    return jsonify({"ok": True, "service": "trend-bot-B"})


load_state()

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", 5000)))
