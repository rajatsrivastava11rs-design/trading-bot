# ================================================================
#  PROFESSIONAL TRADING BOT — Multi-Filter Confluence Strategy
#  Strategy: Trend + Pullback + Volume + Price Action + Claude AI
#  Target win rate: 55-60% | Min R:R: 2:1 | Time: 9:30-14:45 IST
# ================================================================

import os, json, datetime, threading, time, math
import schedule
try:
    import pyotp
    PYOTP_OK = True
except: PYOTP_OK = False

from flask import Flask, jsonify
import anthropic
from SmartApi import SmartConnect

app = Flask(__name__)

# ── Config ────────────────────────────────────────────────────
ANGEL_API_KEY     = os.getenv("ANGEL_API_KEY", "")
ANGEL_CLIENT_ID   = os.getenv("ANGEL_CLIENT_ID", "")
ANGEL_PASSWORD    = os.getenv("ANGEL_PASSWORD", "")
ANGEL_TOTP_TOKEN  = os.getenv("ANGEL_TOTP_TOKEN", "")
ANTHROPIC_API_KEY = os.getenv("ANTHROPIC_API_KEY", "")
DRY_RUN           = os.getenv("DRY_RUN", "true").lower() == "true"
CAPITAL           = float(os.getenv("CAPITAL", "50000"))        # Total capital
RISK_PER_TRADE    = float(os.getenv("RISK_PER_TRADE", "0.01")) # 1% risk per trade
MAX_DAILY_LOSS    = float(os.getenv("MAX_DAILY_LOSS", "500"))
MAX_DAILY_PROFIT  = float(os.getenv("MAX_DAILY_PROFIT", "2000"))
MAX_TRADES_DAY    = int(os.getenv("MAX_TRADES_DAY", "4"))       # Quality > Quantity
PORT              = int(os.getenv("PORT", "5000"))
MIN_RR            = float(os.getenv("MIN_RR", "2.0"))          # Minimum R:R ratio
MIN_SCORE         = int(os.getenv("MIN_SCORE", "5"))           # Need 5/7 filters

# ── Professional Watchlist — Top Nifty 50 Liquid Stocks ───────
WATCHLIST = [
    {"symbol": "RELIANCE",  "token": "2885",   "exchange": "NSE"},
    {"symbol": "HDFCBANK",  "token": "1333",   "exchange": "NSE"},
    {"symbol": "ICICIBANK", "token": "4963",   "exchange": "NSE"},
    {"symbol": "INFY",      "token": "1594",   "exchange": "NSE"},
    {"symbol": "SBIN",      "token": "3045",   "exchange": "NSE"},
    {"symbol": "AXISBANK",  "token": "5900",   "exchange": "NSE"},
    {"symbol": "KOTAKBANK", "token": "1922",   "exchange": "NSE"},
    {"symbol": "TCS",       "token": "11536",  "exchange": "NSE"},
]

# ── State ─────────────────────────────────────────────────────
_session       = None
_daily_pnl     = 0.0
_trades_today  = 0
_positions     = {}
_paused        = False
_log           = []
_scan_count    = 0
_signals_today = []

def log(msg):
    ts = datetime.datetime.now().strftime("%H:%M:%S")
    entry = f"[{ts}] {msg}"
    print(entry)
    _log.append(entry)
    if len(_log) > 150: _log.pop(0)

# ═══════════════════════════════════════════════════════════════
#  SECTION 1: ANGEL ONE SESSION
# ═══════════════════════════════════════════════════════════════
def get_session():
    global _session
    if _session: return _session
    obj = SmartConnect(api_key=ANGEL_API_KEY)
    totp = pyotp.TOTP(ANGEL_TOTP_TOKEN).now() if (ANGEL_TOTP_TOKEN and PYOTP_OK) else ""
    data = obj.generateSession(ANGEL_CLIENT_ID, ANGEL_PASSWORD, totp)
    if not data.get("status"):
        raise Exception(f"Angel One login failed: {data.get('message')}")
    _session = obj
    log("✅ Angel One session active")
    return _session

def get_candles(token, interval="FIFTEEN_MINUTE", count=60):
    obj = get_session()
    now = datetime.datetime.now()
    frm = now - datetime.timedelta(hours=12)
    data = obj.getCandleData({
        "exchange": "NSE", "symboltoken": token,
        "interval": interval,
        "fromdate": frm.strftime("%Y-%m-%d %H:%M"),
        "todate":   now.strftime("%Y-%m-%d %H:%M")
    })
    raw = data.get("data", [])[-count:]
    return [{"time":c[0],"open":c[1],"high":c[2],
              "low":c[3],"close":c[4],"volume":c[5]} for c in raw]

# ═══════════════════════════════════════════════════════════════
#  SECTION 2: PROFESSIONAL INDICATOR ENGINE
# ═══════════════════════════════════════════════════════════════
def ema(values, period):
    if len(values) < period: return [None]*len(values)
    k = 2/(period+1)
    out = [None]*(period-1)
    out.append(sum(values[:period])/period)
    for v in values[period:]:
        out.append(v*k + out[-1]*(1-k))
    return out

def rsi(closes, period=14):
    if len(closes) < period+1: return [None]*len(closes)
    result = [None]*period
    g, l = [], []
    for i in range(1, period+1):
        d = closes[i]-closes[i-1]
        g.append(max(d,0)); l.append(max(-d,0))
    ag=sum(g)/period; al=sum(l)/period
    for i in range(period, len(closes)):
        d = closes[i]-closes[i-1]
        ag=(ag*(period-1)+max(d,0))/period
        al=(al*(period-1)+max(-d,0))/period
        result.append(100 if al==0 else 100-(100/(1+ag/al)))
    return result

def macd(closes):
    e12=ema(closes,12); e26=ema(closes,26)
    ml=[(a-b) if a and b else None for a,b in zip(e12,e26)]
    valid=[v for v in ml if v is not None]
    if len(valid)<9: return ml,[None]*len(ml),[None]*len(ml)
    sl=ema(valid,9)
    pad=len(ml)-len(sl)
    sl=[None]*pad+sl
    hist=[(m-s) if m and s else None for m,s in zip(ml,sl)]
    return ml,sl,hist

def atr(highs, lows, closes, period=14):
    tr=[None]
    for i in range(1,len(closes)):
        tr.append(max(highs[i]-lows[i],
                      abs(highs[i]-closes[i-1]),
                      abs(lows[i]-closes[i-1])))
    valid=[t for t in tr if t]
    if len(valid)<period: return [None]*len(closes)
    result=[None]*period
    val=sum(valid[:period])/period
    result.append(val)
    for i in range(period,len(valid)):
        val=(val*(period-1)+valid[i])/period
        result.append(val)
    while len(result)<len(closes): result.append(result[-1])
    return result

def vwap(candles):
    tv=sum(c["volume"] for c in candles)
    if tv==0: return candles[-1]["close"]
    return sum(((c["high"]+c["low"]+c["close"])/3)*c["volume"] for c in candles)/tv

def last(series, default=None):
    for v in reversed(series):
        if v is not None: return round(v,2)
    return default

def ema_slope(series, lookback=5):
    """Positive = uptrend, Negative = downtrend"""
    vals = [v for v in series[-lookback:] if v]
    if len(vals)<2: return 0
    return vals[-1]-vals[0]

# ═══════════════════════════════════════════════════════════════
#  SECTION 3: PROFESSIONAL SIGNAL SCORING ENGINE
#  7 filters — need MIN_SCORE (default 5) to proceed
# ═══════════════════════════════════════════════════════════════
def score_signal(ind, action):
    """
    Returns (score, details_dict)
    Each filter: 1 point if passed, 0 if failed
    """
    scores = {}

    # ── Filter 1: EMA Trend Alignment ─────────────────────────
    # EMA21 slope must match trade direction
    slope = ema_slope(ind["ema21_series"])
    if action == "BUY":
        scores["ema_trend"] = 1 if slope > 0 else 0
    else:
        scores["ema_trend"] = 1 if slope < 0 else 0

    # ── Filter 2: EMA9 vs EMA21 Position ──────────────────────
    e9, e21 = ind["ema9"], ind["ema21"]
    if action == "BUY":
        scores["ema_cross"] = 1 if (e9 and e21 and e9 > e21) else 0
    else:
        scores["ema_cross"] = 1 if (e9 and e21 and e9 < e21) else 0

    # ── Filter 3: RSI Sweet Zone ───────────────────────────────
    # BUY: 45-68 (not overbought, has room to run)
    # SELL: 32-55 (not oversold, has room to fall)
    rsi_val = ind["rsi"]
    if rsi_val:
        if action == "BUY":
            scores["rsi"] = 1 if 45 <= rsi_val <= 68 else 0
        else:
            scores["rsi"] = 1 if 32 <= rsi_val <= 55 else 0
    else:
        scores["rsi"] = 0

    # ── Filter 4: Price vs VWAP ────────────────────────────────
    price, vwap_val = ind["close"], ind["vwap"]
    if action == "BUY":
        scores["vwap"] = 1 if price > vwap_val else 0
    else:
        scores["vwap"] = 1 if price < vwap_val else 0

    # ── Filter 5: MACD Histogram Direction ────────────────────
    hist_now  = ind["macd_hist"]
    hist_prev = ind["macd_hist_prev"]
    if hist_now is not None and hist_prev is not None:
        if action == "BUY":
            scores["macd"] = 1 if (hist_now > 0 or hist_now > hist_prev) else 0
        else:
            scores["macd"] = 1 if (hist_now < 0 or hist_now < hist_prev) else 0
    else:
        scores["macd"] = 0

    # ── Filter 6: Volume Surge ─────────────────────────────────
    vol_ratio = ind["vol_ratio"]
    scores["volume"] = 1 if (vol_ratio and vol_ratio >= 1.4) else 0

    # ── Filter 7: Candle Quality (no doji/indecision) ─────────
    candle_range = ind["high"] - ind["low"]
    body = abs(ind["close"] - ind["open"])
    if candle_range > 0:
        body_pct = body/candle_range
        scores["candle"] = 1 if body_pct >= 0.45 else 0
    else:
        scores["candle"] = 0

    total = sum(scores.values())
    return total, scores

def find_atr_levels(entry, atr_val, action):
    """Calculate professional SL and targets using ATR"""
    if not atr_val or atr_val == 0:
        atr_val = entry * 0.005  # fallback: 0.5% of price

    sl_dist  = round(1.5 * atr_val, 2)   # SL = 1.5x ATR
    t1_dist  = round(2.0 * sl_dist, 2)   # T1 = 2:1 R:R
    t2_dist  = round(3.0 * sl_dist, 2)   # T2 = 3:1 R:R

    if action == "BUY":
        return {
            "sl":  round(entry - sl_dist, 2),
            "t1":  round(entry + t1_dist, 2),
            "t2":  round(entry + t2_dist, 2),
            "rr":  round(t1_dist/sl_dist, 2),
            "sl_dist": sl_dist
        }
    else:
        return {
            "sl":  round(entry + sl_dist, 2),
            "t1":  round(entry - t1_dist, 2),
            "t2":  round(entry - t2_dist, 2),
            "rr":  round(t1_dist/sl_dist, 2),
            "sl_dist": sl_dist
        }

# ═══════════════════════════════════════════════════════════════
#  SECTION 4: CLAUDE AI — SENIOR RISK MANAGER
# ═══════════════════════════════════════════════════════════════
def claude_validate(symbol, action, ind, score, scores, levels):
    client = anthropic.Anthropic(api_key=ANTHROPIC_API_KEY)
    prompt = f"""You are a SENIOR RISK MANAGER with 10+ years of Indian equity trading experience.
A trading bot has flagged a potential trade. Your job: APPROVE or REJECT it.
Be STRICT. Reject marginal setups. Only approve high-conviction trades.

=== TRADE PROPOSAL ===
Symbol:  {symbol}
Signal:  {action}
Score:   {score}/7 filters passed → {scores}

=== MARKET DATA ===
Price:   ₹{ind['close']} | Open: ₹{ind['open']} | High: ₹{ind['high']} | Low: ₹{ind['low']}
EMA 9:   {ind['ema9']} | EMA 21: {ind['ema21']}
RSI:     {ind['rsi']} | VWAP: {ind['vwap']}
MACD:    {ind['macd']} | Signal: {ind['macd_sig']} | Hist: {ind['macd_hist']}
ATR:     {ind['atr']} | Volume ratio: {ind['vol_ratio']}x avg

=== PROPOSED LEVELS ===
Entry:   ₹{ind['close']}
SL:      ₹{levels['sl']} (distance: ₹{levels['sl_dist']})
T1:      ₹{levels['t1']} (R:R = {levels['rr']}:1)
T2:      ₹{levels['t2']} (R:R = 3:1)

=== CHECKLIST FOR APPROVAL ===
- Is RSI in a healthy zone (not extreme)?
- Is the trend genuinely clear or choppy?
- Is volume confirmation real or marginal?
- Are SL levels logical (not too tight/wide)?
- Is R:R genuinely ≥ 2:1?

Respond ONLY in JSON (no extra text):
{{"approve": true|false, "confidence": "HIGH|MEDIUM|LOW",
  "adjusted_sl": <price or null if ok>,
  "adjusted_t1": <price or null if ok>,
  "reason": "<1-2 lines why approve/reject>",
  "risk_note": "<one key risk to watch>"}}

approve=true ONLY if: score≥5 AND rr≥2.0 AND setup is genuinely clean."""

    try:
        resp = client.messages.create(
            model="claude-sonnet-4-6", max_tokens=400,
            messages=[{"role":"user","content":prompt}]
        )
        raw = resp.content[0].text.strip()
        if "```" in raw:
            raw = raw.split("```")[1]
            if raw.startswith("json"): raw=raw[4:]
        return json.loads(raw.strip())
    except Exception as e:
        log(f"❌ Claude error: {e}")
        return {"approve": False, "confidence": "LOW", "reason": f"Claude error: {e}"}

# ═══════════════════════════════════════════════════════════════
#  SECTION 5: RISK & ORDER MANAGEMENT
# ═══════════════════════════════════════════════════════════════
def check_guards():
    now = datetime.datetime.now()
    mins = now.hour*60 + now.minute
    if mins < 9*60+30:     return False, "Before 9:30 AM — avoid opening volatility"
    if mins > 14*60+45:    return False, "After 2:45 PM — no new trades"
    if _daily_pnl <= -MAX_DAILY_LOSS:  return False, f"Daily loss ₹{abs(_daily_pnl):.0f} hit"
    if _daily_pnl >= MAX_DAILY_PROFIT: return False, f"Daily profit ₹{_daily_pnl:.0f} locked"
    if _trades_today >= MAX_TRADES_DAY: return False, f"Max {MAX_TRADES_DAY} trades/day"
    if len(_positions) >= 2: return False, "Max 2 concurrent positions"
    return True, "OK"

def calc_qty(entry, sl):
    """1% of capital = max risk per trade"""
    risk_amount = CAPITAL * RISK_PER_TRADE
    sl_dist = abs(entry - sl)
    if sl_dist == 0: return 1
    qty = int(risk_amount / sl_dist)
    return max(1, qty)

def place_order(symbol, token, side, entry, sl, t1, t2, rr, confidence):
    global _trades_today, _positions
    qty = calc_qty(entry, sl)
    risk = abs(entry - sl) * qty

    if DRY_RUN:
        oid = f"DRY_{datetime.datetime.now().strftime('%H%M%S')}"
        log(f"🟡 DRY {side} {qty}x {symbol} | Entry:₹{entry} SL:₹{sl} T1:₹{t1} T2:₹{t2}")
        log(f"   Risk: ₹{risk:.0f} | R:R: {rr} | Confidence: {confidence}")
    else:
        try:
            obj = get_session()
            resp = obj.placeOrder({
                "variety":"NORMAL","tradingsymbol":symbol,"symboltoken":token,
                "transactiontype":side,"exchange":"NSE","ordertype":"MARKET",
                "producttype":"INTRADAY","duration":"DAY",
                "price":"0","squareoff":"0","stoploss":"0","quantity":str(qty)
            })
            oid = resp.get("data",{}).get("orderid","?")
            log(f"✅ LIVE {side} {qty}x {symbol} | OrderID:{oid}")
        except Exception as e:
            log(f"❌ Order failed {symbol}: {e}")
            return

    _trades_today += 1
    _positions[symbol] = {
        "side":side,"entry":entry,"sl":sl,"t1":t1,"t2":t2,
        "qty":qty,"risk":round(risk,2),"rr":rr,
        "order_id":oid,"time":datetime.datetime.now().strftime("%H:%M"),
        "confidence":confidence
    }
    _signals_today.append({
        "symbol":symbol,"side":side,"entry":entry,"sl":sl,
        "t1":t1,"rr":rr,"time":datetime.datetime.now().strftime("%H:%M"),
        "status":"OPEN"
    })

def squareoff_all():
    global _positions
    if not _positions:
        log("📭 No open positions"); return
    log(f"🔔 SQUAREOFF — {len(_positions)} positions")
    for sym, pos in list(_positions.items()):
        exit_side = "SELL" if pos["side"]=="BUY" else "BUY"
        log(f"   → {exit_side} {pos['qty']}x {sym}")
        if not DRY_RUN:
            try:
                get_session().placeOrder({
                    "variety":"NORMAL","tradingsymbol":sym,"symboltoken":"",
                    "transactiontype":exit_side,"exchange":"NSE",
                    "ordertype":"MARKET","producttype":"INTRADAY",
                    "duration":"DAY","price":"0","squareoff":"0",
                    "stoploss":"0","quantity":str(pos["qty"])
                })
            except Exception as e:
                log(f"   ❌ {sym} squareoff error: {e}")
    _positions.clear()
    log(f"✅ All squared off | Day P&L: ₹{_daily_pnl:.2f}")

# ═══════════════════════════════════════════════════════════════
#  SECTION 6: MAIN SCANNER
# ═══════════════════════════════════════════════════════════════
def scan_symbol(sym_info):
    global _scan_count
    symbol = sym_info["symbol"]
    token  = sym_info["token"]

    # Skip if already in position
    if symbol in _positions:
        return

    try:
        candles = get_candles(token, count=60)
    except Exception as e:
        log(f"   ❌ {symbol} data error: {e}"); return

    if len(candles) < 40:
        return

    closes  = [c["close"]  for c in candles]
    highs   = [c["high"]   for c in candles]
    lows    = [c["low"]    for c in candles]
    volumes = [c["volume"] for c in candles]
    opens   = [c["open"]   for c in candles]

    # Calculate all indicators
    e9_series  = ema(closes, 9)
    e21_series = ema(closes, 21)
    rsi_s      = rsi(closes, 14)
    atr_s      = atr(highs, lows, closes, 14)
    ml, sl, hist = macd(closes)
    vwap_val   = vwap(candles)
    vol_avg    = sum(volumes[-20:])/20

    e9_now  = last(e9_series)
    e21_now = last(e21_series)

    # ── Detect fresh EMA crossover (within last 3 candles) ────
    cross_bar = None
    for i in range(-3, 0):
        try:
            if e9_series[i] and e21_series[i] and e9_series[i-1] and e21_series[i-1]:
                if e9_series[i-1] <= e21_series[i-1] and e9_series[i] > e21_series[i]:
                    cross_bar = "BUY"
                elif e9_series[i-1] >= e21_series[i-1] and e9_series[i] < e21_series[i]:
                    cross_bar = "SELL"
        except: pass

    if not cross_bar:
        return

    action = cross_bar
    log(f"👀 {symbol} — fresh {action} crossover (checking quality...)")

    # Build indicator dict
    ind = {
        "close": closes[-1], "open": opens[-1],
        "high": highs[-1],   "low": lows[-1],
        "ema9": e9_now, "ema21": e21_now,
        "ema9_series": e9_series, "ema21_series": e21_series,
        "rsi": last(rsi_s),
        "atr": last(atr_s),
        "macd": last(ml), "macd_sig": last(sl),
        "macd_hist": last(hist),
        "macd_hist_prev": hist[-2] if len(hist)>1 else None,
        "vwap": round(vwap_val, 2),
        "vol_ratio": round(volumes[-1]/vol_avg, 2) if vol_avg > 0 else 0,
    }

    # ── Score the signal ──────────────────────────────────────
    score, scores = score_signal(ind, action)
    log(f"   📊 Score: {score}/7 | {scores}")

    if score < MIN_SCORE:
        log(f"   ⛔ Score too low ({score}<{MIN_SCORE}) — skipping {symbol}")
        return

    # ── Calculate ATR-based levels ────────────────────────────
    levels = find_atr_levels(closes[-1], ind["atr"], action)

    if levels["rr"] < MIN_RR:
        log(f"   ⛔ R:R {levels['rr']} < {MIN_RR} — skipping")
        return

    log(f"   ✅ Score OK! R:R={levels['rr']} | Asking Claude...")

    # ── Claude Senior Risk Manager validation ────────────────
    verdict = claude_validate(symbol, action, ind, score, scores, levels)
    log(f"   🤖 Claude: approve={verdict.get('approve')} | {verdict.get('confidence')} | {verdict.get('reason')}")

    if verdict.get("risk_note"):
        log(f"   ⚠️  Risk: {verdict.get('risk_note')}")

    if not verdict.get("approve"):
        log(f"   ❌ Claude rejected — {verdict.get('reason')}")
        return

    # ── Use Claude's adjusted levels if provided ─────────────
    sl_final = verdict.get("adjusted_sl") or levels["sl"]
    t1_final = verdict.get("adjusted_t1") or levels["t1"]

    # ── Place order ───────────────────────────────────────────
    ok, reason = check_guards()
    if not ok:
        log(f"   🚫 Guards: {reason}"); return

    place_order(
        symbol=symbol, token=token, side=action,
        entry=closes[-1], sl=sl_final,
        t1=t1_final, t2=levels["t2"],
        rr=levels["rr"], confidence=verdict.get("confidence")
    )

def run_scan():
    global _scan_count
    now = datetime.datetime.now()
    mins = now.hour*60+now.minute
    if not (9*60+15 <= mins <= 15*60+10): return
    if _paused:
        log("⏸️ Paused — scan skipped"); return

    _scan_count += 1
    log(f"\n{'='*45}")
    log(f"🔄 SCAN #{_scan_count} — {now.strftime('%H:%M IST')}")
    log(f"   Trades: {_trades_today}/{MAX_TRADES_DAY} | P&L: ₹{_daily_pnl:.0f}")
    log(f"{'='*45}")

    ok, reason = check_guards()
    if not ok:
        log(f"🚫 {reason}"); return

    for s in WATCHLIST:
        try: scan_symbol(s)
        except Exception as e: log(f"❌ {s['symbol']} error: {e}")

    log(f"✅ Scan #{_scan_count} complete\n")

# ═══════════════════════════════════════════════════════════════
#  SECTION 7: FLASK — MOBILE DASHBOARD
# ═══════════════════════════════════════════════════════════════
@app.route("/")
def home():
    mode = "🟡 DRY RUN" if DRY_RUN else "🔴 LIVE"
    pnl_color = "#7fff7f" if _daily_pnl >= 0 else "#ff7f7f"
    pos_html = ""
    for sym,p in _positions.items():
        pos_html += f"<div style='background:#1a2a1a;padding:10px;margin:6px 0;border-radius:8px;border-left:3px solid #7fff7f'>"
        pos_html += f"<b>{sym}</b> {p['side']} {p['qty']}qty @ ₹{p['entry']}<br>"
        pos_html += f"SL:₹{p['sl']} T1:₹{p['t1']} T2:₹{p['t2']}<br>"
        pos_html += f"R:R {p['rr']} | Risk:₹{p['risk']} | {p['confidence']}</div>"

    sig_html = ""
    for s in reversed(_signals_today[-5:]):
        sig_html += f"<div style='font-size:12px;color:#aaa;margin:3px 0'>{s['time']} {s['symbol']} {s['side']} @ ₹{s['entry']} | T1:₹{s['t1']} | RR:{s['rr']}</div>"

    return f"""<!DOCTYPE html><html><head><title>Pro Trading Bot</title>
<meta name="viewport" content="width=device-width,initial-scale=1">
<meta http-equiv="refresh" content="60">
<style>*{{box-sizing:border-box}}body{{font-family:sans-serif;background:#0a0a0a;color:#eee;padding:14px;margin:0}}
h2{{margin:0 0 4px;font-size:18px}}
.stat{{display:inline-block;background:#1a1a1a;border-radius:8px;padding:8px 14px;margin:4px;text-align:center}}
.stat-val{{font-size:20px;font-weight:bold}}
.stat-lbl{{font-size:11px;color:#888}}
a{{display:block;padding:13px;margin:6px 0;border-radius:8px;text-decoration:none;font-size:15px;font-weight:500;text-align:center}}
.green{{background:#0d2a0d;color:#7fff7f;border:1px solid #1a4a1a}}
.yellow{{background:#2a2a0d;color:#ffff7f;border:1px solid #4a4a1a}}
.red{{background:#2a0d0d;color:#ff7f7f;border:1px solid #4a1a1a}}
.blue{{background:#0d1a2a;color:#7fbfff;border:1px solid #1a2a4a}}</style>
</head><body>
<h2>🤖 Pro Trading Bot</h2>
<div style="font-size:12px;color:#888;margin-bottom:12px">{mode} | Auto-refreshes 60s</div>

<div>
<div class="stat"><div class="stat-val" style="color:{pnl_color}">₹{_daily_pnl:.0f}</div><div class="stat-lbl">Day P&L</div></div>
<div class="stat"><div class="stat-val">{_trades_today}/{MAX_TRADES_DAY}</div><div class="stat-lbl">Trades</div></div>
<div class="stat"><div class="stat-val">{len(_positions)}</div><div class="stat-lbl">Open</div></div>
<div class="stat"><div class="stat-val">#{_scan_count}</div><div class="stat-lbl">Scans</div></div>
</div>

{f'<div style="margin:12px 0"><div style="color:#888;font-size:12px;margin-bottom:4px">OPEN POSITIONS</div>{pos_html}</div>' if _positions else '<div style="color:#555;font-size:13px;margin:12px 0">No open positions</div>'}

{f'<div style="margin:12px 0"><div style="color:#888;font-size:12px;margin-bottom:4px">TODAY\'S SIGNALS</div>{sig_html}</div>' if _signals_today else ''}

<a href="/scan" class="green">🔍 Force Scan Now</a>
<a href="/log" class="blue">📋 Live Log (auto-refresh)</a>
<a href="/status" class="blue">📊 Full Status (JSON)</a>
<a href="/pause" class="yellow">⏸️ {'Resume Bot' if _paused else 'Pause Bot'}</a>
<a href="/squareoff" class="red">🔴 Square Off ALL</a>
<div style="font-size:11px;color:#444;margin-top:12px">Capital: ₹{CAPITAL:,.0f} | Risk/trade: {RISK_PER_TRADE*100:.0f}% | Min score: {MIN_SCORE}/7</div>
</body></html>"""

@app.route("/ping")
def ping():
    return jsonify({"status":"alive","mode":"DRY_RUN" if DRY_RUN else "LIVE",
                    "paused":_paused,"time":datetime.datetime.now().strftime("%H:%M:%S"),
                    "trades_today":_trades_today,"daily_pnl":_daily_pnl})

@app.route("/status")
def status():
    return jsonify({"mode":"DRY_RUN" if DRY_RUN else "LIVE","paused":_paused,
                    "capital":CAPITAL,"risk_per_trade":RISK_PER_TRADE,
                    "trades_today":_trades_today,"daily_pnl":_daily_pnl,
                    "open_positions":_positions,"signals_today":_signals_today,
                    "scan_count":_scan_count,"watchlist":[w["symbol"] for w in WATCHLIST]})

@app.route("/log")
def show_log():
    lines="<br>".join(reversed(_log[-60:]))
    return f"""<!DOCTYPE html><html><head><title>Bot Log</title>
<meta name="viewport" content="width=device-width,initial-scale=1">
<meta http-equiv="refresh" content="20">
<style>body{{font-family:monospace;background:#0a0a0a;color:#90ee90;padding:12px;font-size:12px}}
a{{color:#7fbfff}}</style></head><body>
<a href="/">← Dashboard</a> &nbsp;<small style="color:#555">Refreshes 20s</small><br><br>
{lines or '<span style="color:#555">No activity yet</span>'}
</body></html>"""

@app.route("/scan")
def manual_scan():
    t=threading.Thread(target=run_scan,daemon=True); t.start()
    return """<!DOCTYPE html><html><head><meta http-equiv="refresh" content="3;url=/log">
<style>body{background:#0a0a0a;color:#7fff7f;font-family:sans-serif;padding:20px}</style></head>
<body>✅ Scan triggered! → <a href="/log" style="color:#7fbfff">View Log</a></body></html>"""

@app.route("/pause")
def pause():
    global _paused; _paused = not _paused
    status = "PAUSED" if _paused else "RESUMED"
    log(f"{'⏸️' if _paused else '▶️'} Bot {status}")
    return f"""<!DOCTYPE html><html><head><meta http-equiv="refresh" content="2;url=/"></head>
<body style="background:#0a0a0a;color:#ffff7f;padding:20px">{status}. Redirecting...</body></html>"""

@app.route("/squareoff")
def manual_sq():
    squareoff_all()
    return """<!DOCTYPE html><html><head><meta http-equiv="refresh" content="2;url=/"></head>
<body style="background:#0a0a0a;color:#ff7f7f;padding:20px">Squaring off... Redirecting...</body></html>"""

# ═══════════════════════════════════════════════════════════════
#  SECTION 8: SCHEDULER & STARTUP
# ═══════════════════════════════════════════════════════════════
def run_scheduler():
    schedule.every(15).minutes.do(run_scan)
    schedule.every().day.at("14:45").do(squareoff_all)
    schedule.every().day.at("09:15").do(lambda: log("🔔 Market open — bot active"))
    log(f"⏰ Scheduler: scan every 15min | auto-squareoff 14:45")
    while True:
        schedule.run_pending()
        time.sleep(30)

if __name__ == "__main__":
    log("="*50)
    log(f"🚀 PRO TRADING BOT STARTED")
    log(f"   Mode:      {'DRY RUN 🟡' if DRY_RUN else 'LIVE 🔴'}")
    log(f"   Capital:   ₹{CAPITAL:,.0f}")
    log(f"   Risk/trade: {RISK_PER_TRADE*100:.0f}% = ₹{CAPITAL*RISK_PER_TRADE:,.0f}")
    log(f"   Strategy:  7-Filter Confluence | Min score: {MIN_SCORE}/7 | Min R:R: {MIN_RR}")
    log(f"   Stocks:    {[w['symbol'] for w in WATCHLIST]}")
    log(f"   Hours:     9:30 AM — 2:45 PM IST")
    log("="*50)
    threading.Thread(target=run_scheduler, daemon=True).start()
    app.run(host="0.0.0.0", port=PORT, debug=False)
