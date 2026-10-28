-- Prove2me | solution 1 for BitcoinBlockV2.futureTime_transient
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T15:12:49.990044+00:00
-- url     : https://prove2.me/submissions/67f60fdb-0811-46e4-9db3-e02553c05326

import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinSer
open BitcoinBlockV2 in
theorem S190BLK_acc_ne_ft (S : ChainState) (b : BitcoinSer.Block) :
    (if !checkBlock b then Outcome.invalid
    else if !contextualCheckBlock S b then .invalid
    else match connectBlock S b with
      | none => .invalid
      | some (u, undo) => .accept ⟨S.headers ++ [b.header], u⟩ undo) ≠ .futureTime := by
  split
  · simp
  · split
    · simp
    · split <;> simp

open BitcoinBlockV2 in
theorem S190BLK_ft_iff (S : ChainState) (b : BitcoinSer.Block) (now : Int) :
    validate S b now = .futureTime ↔ acceptHeader S b.header now = .futureTime := by
  unfold validate
  split
  · rename_i h
    rw [h]
    constructor
    · intro h2; exact absurd h2 (S190BLK_acc_ne_ft S b)
    · intro h2; cases h2
  all_goals rfl


open BitcoinBlockV2 in
theorem S190BLK_val_congr (S : ChainState) (b : BitcoinSer.Block) (n m : Int)
    (h : acceptHeader S b.header n = acceptHeader S b.header m) : validate S b n = validate S b m := by
  unfold validate; rw [h]

open BitcoinBlockV2 in
theorem S190BLK_ah_clock (S : ChainState) (h : BitcoinSer.Header) (now now' : Int)
    (hn : acceptHeader S h now ≠ .futureTime) (hle : now ≤ now') :
    acceptHeader S h now' = acceptHeader S h now := by
  unfold acceptHeader at hn ⊢
  by_cases h1 : checkHeaderPow h = true
  · by_cases h2 : h.prevBlock = S.tipHash
    · by_cases h3 : BitVec.ofNat 32 h.bits = S.requiredBits
      · by_cases h4 : (h.time : Int) ≤ S.mtp
        · simp [h1, h2, h3, h4]
        · by_cases h5 : now + MAX_FUTURE_BLOCK_TIME < (h.time : Int)
          · simp [h1, h2, h3, h4, h5] at hn
          · have : ¬ now' + MAX_FUTURE_BLOCK_TIME < (h.time : Int) := by omega
            simp [h1, h2, h3, h4, h5, this]
      · simp [h1, h2, h3]
    · simp [h1, h2]
  · simp [h1]

open BitcoinBlockV2 in
open BitcoinBlockV2 in
theorem S190BLK_ah_ft (S : ChainState) (h : BitcoinSer.Header) (now now' : Int)
    (hn : acceptHeader S h now = .futureTime) (hle : (h.time : Int) ≤ now' + MAX_FUTURE_BLOCK_TIME) :
    acceptHeader S h now' ≠ .futureTime ∧
    acceptHeader S h now' = acceptHeader S h ((h.time : Int) - MAX_FUTURE_BLOCK_TIME) := by
  unfold acceptHeader at hn ⊢
  have a : ¬ now' + MAX_FUTURE_BLOCK_TIME < (h.time : Int) := by omega
  have b : ¬ (h.time : Int) - MAX_FUTURE_BLOCK_TIME + MAX_FUTURE_BLOCK_TIME < (h.time : Int) := by omega
  by_cases h1 : checkHeaderPow h = true
  · by_cases h2 : h.prevBlock = S.tipHash
    · by_cases h3 : BitVec.ofNat 32 h.bits = S.requiredBits
      · by_cases h4 : (h.time : Int) ≤ S.mtp
        · simp [h1, h2, h3, h4] at hn
        · simp only [h1, h2, h3, h4, a, b, if_false, Bool.not_true, ne_eq, not_true_eq_false, not_false_eq_true, if_true]
          refine ⟨?_, trivial⟩
          by_cases hv : BitcoinHeader.versionOutdated h.version S.tipHeight = true
          · rw [if_pos hv]; intro hc; cases hc
          · rw [if_neg hv]; intro hc; cases hc
      · simp [h1, h2, h3] at hn
    · simp [h1, h2] at hn
  · simp [h1] at hn

open BitcoinBlockV2 in
open BitcoinBlockV2 in
theorem solution (S : ChainState) (b : BitcoinSer.Block) (now : Int)
    (h : BitcoinBlockV2.validate S b now = .futureTime) (now' : Int)
    (hle : (b.header.time : Int) ≤ now' + MAX_FUTURE_BLOCK_TIME) :
    BitcoinBlockV2.validate S b now' ≠ .futureTime ∧
    BitcoinBlockV2.validate S b now' = BitcoinBlockV2.validate S b ((b.header.time : Int) - MAX_FUTURE_BLOCK_TIME) := by
  have h' := (S190BLK_ft_iff S b now).mp h
  obtain ⟨k1, k2⟩ := S190BLK_ah_ft S b.header now now' h' hle
  refine ⟨?_, S190BLK_val_congr _ _ _ _ k2⟩
  intro hc
  exact k1 ((S190BLK_ft_iff S b now').mp hc)
