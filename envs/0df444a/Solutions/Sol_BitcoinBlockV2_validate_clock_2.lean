-- Prove2me | solution 2 for BitcoinBlockV2.validate_clock
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-28T15:21:56.570847+00:00
-- url     : https://prove2.me/submissions/df5906c4-9029-4fa2-9bc3-25e6dc957a8e

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

/-- The clock only matters through the future-time test: an outcome other than `futureTime` is the
same at every later clock reading. -/
theorem solution (S : ChainState) (b : BitcoinSer.Block) (now now' : Int)
    (h : BitcoinBlockV2.validate S b now ≠ .futureTime) (hle : now ≤ now') :
    BitcoinBlockV2.validate S b now' = BitcoinBlockV2.validate S b now := by
  rcases acceptHeader_clock' S b.header now now' hle with hf | he
  · exfalso; apply h; unfold validate; rw [hf]
  · unfold validate; rw [he]
