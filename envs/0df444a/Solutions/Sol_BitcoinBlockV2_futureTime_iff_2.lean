-- Prove2me | solution 2 for BitcoinBlockV2.futureTime_iff
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-28T15:18:24.112284+00:00
-- url     : https://prove2.me/submissions/10a00f8e-b518-448f-a596-beec0140784b

import Definitions.Def_BitcoinBlockV2
import Theorems.Thm_BitcoinPow_checkProofOfWork_iff
import Theorems.Thm_BitcoinHeader_versionOutdated_iff
import Theorems.Thm_BitcoinSubsidy_core_eq_spec
import Theorems.Thm_BitcoinBIP68_fold_acceptance
import Theorems.Thm_BitcoinBIP68_decode_sequence

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

/-- `BLOCK_TIME_FUTURE` is reported exactly when the header is sound up to the clock test and the
time exceeds the local clock by more than two hours. -/
theorem solution (S : ChainState) (b : BitcoinSer.Block) (now : Int) :
    BitcoinBlockV2.validate S b now = .futureTime ↔
      BitcoinBlockV2.checkHeaderPow b.header = true ∧ b.header.prevBlock = S.tipHash ∧
      BitVec.ofNat 32 b.header.bits = S.requiredBits ∧ S.mtp < (b.header.time : Int) ∧
      now + MAX_FUTURE_BLOCK_TIME < (b.header.time : Int) := by
  rw [futureTime_iff']
  constructor
  · rintro ⟨a, b, c, d, e⟩; exact ⟨a, b, c, by omega, e⟩
  · rintro ⟨a, b, c, d, e⟩; exact ⟨a, b, c, by omega, e⟩
