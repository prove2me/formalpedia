-- Prove2me | solution 2 for BitcoinBlockV2.futureTime_transient
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-28T15:21:57.523146+00:00
-- url     : https://prove2.me/submissions/07a7c2a4-ec2c-4bdb-ad12-fff4e2978b95

import Definitions.Def_BitcoinBlockV2
import Theorems.Thm_BitcoinPow_checkProofOfWork_iff
import Theorems.Thm_BitcoinHeader_versionOutdated_iff
import Theorems.Thm_BitcoinSubsidy_core_eq_spec
import Theorems.Thm_BitcoinBIP68_fold_acceptance
import Theorems.Thm_BitcoinBIP68_decode_sequence
import Theorems.Thm_BitcoinBlockV2_futureTime_iff

open BitcoinBlockV2

/-- The initial state is well formed. -/
private theorem initial_wellFormed : BitcoinBlockV2.WellFormed BitcoinBlockV2.initialState := by
  refine ⟨rfl, List.nodup_nil, ?_⟩
  intro e he; cases he

/-- `AcceptBlockHeader` on top of the tip accepts exactly when the proof of work holds, the parent is
the tip, and the Header mission's `ContextualCheckBlockHeader` holds with the chain's median time past
and required work. -/
private theorem acceptHeader_eq_iff (S : ChainState) (h : BitcoinSer.Header) (now : Int) :
    BitcoinBlockV2.acceptHeader S h now = .accept S [] ↔
      BitcoinBlockV2.checkHeaderPow h = true ∧ h.prevBlock = S.tipHash ∧
      BitVec.ofNat 32 h.bits = S.requiredBits ∧ ¬ ((h.time : Int) ≤ S.mtp) ∧
      ¬ (now + MAX_FUTURE_BLOCK_TIME < (h.time : Int)) ∧
      BitcoinHeader.versionOutdated h.version S.tipHeight = false := by
  unfold acceptHeader
  simp only [Bool.not_eq_true']
  by_cases h1 : checkHeaderPow h = false <;> by_cases h2 : h.prevBlock = S.tipHash <;>
    by_cases h3 : BitVec.ofNat 32 h.bits = S.requiredBits <;> by_cases h4 : (h.time : Int) ≤ S.mtp <;>
    by_cases h5 : now + MAX_FUTURE_BLOCK_TIME < (h.time : Int) <;>
    by_cases h6 : BitcoinHeader.versionOutdated h.version S.tipHeight = true <;>
    simp only [h1, h2, h3, h4, h5, h6, ite_true, ite_false, ne_eq, not_true_eq_false, not_false_eq_true] <;>
    simp_all

private theorem futureTime_iff' (S : ChainState) (b : BitcoinSer.Block) (now : Int) :
    BitcoinBlockV2.validate S b now = .futureTime ↔
      BitcoinBlockV2.checkHeaderPow b.header = true ∧ b.header.prevBlock = S.tipHash ∧
      BitVec.ofNat 32 b.header.bits = S.requiredBits ∧ ¬ ((b.header.time : Int) ≤ S.mtp) ∧
      now + MAX_FUTURE_BLOCK_TIME < (b.header.time : Int) := by
  unfold validate acceptHeader
  simp only [Bool.not_eq_true']
  by_cases h1 : checkHeaderPow b.header = false <;> by_cases h2 : b.header.prevBlock = S.tipHash <;>
    by_cases h3 : BitVec.ofNat 32 b.header.bits = S.requiredBits <;> by_cases h4 : (b.header.time : Int) ≤ S.mtp <;>
    by_cases h5 : now + MAX_FUTURE_BLOCK_TIME < (b.header.time : Int) <;>
    by_cases h6 : BitcoinHeader.versionOutdated b.header.version S.tipHeight = true <;>
    simp only [h1, h2, h3, h4, h5, h6, ite_true, ite_false, ne_eq, not_true_eq_false, not_false_eq_true] <;>
    (try simp_all)
  all_goals (split <;> (try split) <;> (try split) <;> simp_all)

private theorem acceptHeader_clock (S : ChainState) (h : BitcoinSer.Header) (now now' : Int)
    (h1 : ¬ now + MAX_FUTURE_BLOCK_TIME < (h.time : Int)) (h2 : ¬ now' + MAX_FUTURE_BLOCK_TIME < (h.time : Int)) :
    BitcoinBlockV2.acceptHeader S h now' = BitcoinBlockV2.acceptHeader S h now := by
  unfold acceptHeader
  simp only [h1, h2, ite_false]

private theorem acceptHeader_clock' (S : ChainState) (h : BitcoinSer.Header) (now now' : Int) (hle : now ≤ now') :
    BitcoinBlockV2.acceptHeader S h now = .futureTime ∨
    BitcoinBlockV2.acceptHeader S h now' = BitcoinBlockV2.acceptHeader S h now := by
  by_cases hf : now + MAX_FUTURE_BLOCK_TIME < (h.time : Int)
  · unfold acceptHeader
    simp only [Bool.not_eq_true']
    by_cases h1 : checkHeaderPow h = false <;> by_cases h2 : h.prevBlock = S.tipHash <;>
      by_cases h3 : BitVec.ofNat 32 h.bits = S.requiredBits <;> by_cases h4 : (h.time : Int) ≤ S.mtp <;>
      simp only [h1, h2, h3, h4, hf, ite_true, ite_false, ne_eq, not_true_eq_false, not_false_eq_true] <;>
      simp_all
  · exact Or.inr (acceptHeader_clock S h now now' hf (by omega))

/-- A future-time rejection is transient: once the clock reaches the block's time minus two hours
the block is no longer rejected for its time, and its outcome is then fixed. -/
theorem solution (S : ChainState) (b : BitcoinSer.Block) (now : Int)
    (h : BitcoinBlockV2.validate S b now = .futureTime) (now' : Int)
    (hle : (b.header.time : Int) ≤ now' + MAX_FUTURE_BLOCK_TIME) :
    BitcoinBlockV2.validate S b now' ≠ .futureTime ∧
    BitcoinBlockV2.validate S b now' = BitcoinBlockV2.validate S b ((b.header.time : Int) - MAX_FUTURE_BLOCK_TIME) := by
  have hc := (futureTime_iff S b now).1 h
  have key : ∀ t, (b.header.time : Int) ≤ t + MAX_FUTURE_BLOCK_TIME → validate S b t ≠ .futureTime := by
    intro t ht hf
    have := (futureTime_iff S b t).1 hf
    omega
  refine ⟨key now' hle, ?_⟩
  unfold validate
  rw [acceptHeader_clock S b.header ((b.header.time : Int) - MAX_FUTURE_BLOCK_TIME) now' (by omega) (by omega)]
