-- Prove2me | solution 2 for BitcoinBlockV2.checkBlock_iff
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-28T15:22:59.651898+00:00
-- url     : https://prove2.me/submissions/52298534-cb6c-4917-9ef9-0c21e6427f10

import Definitions.Def_BitcoinBlockV2
import Theorems.Thm_BitcoinPow_checkProofOfWork_iff
import Theorems.Thm_BitcoinHeader_versionOutdated_iff
import Theorems.Thm_BitcoinSubsidy_core_eq_spec
import Theorems.Thm_BitcoinBIP68_fold_acceptance
import Theorems.Thm_BitcoinBIP68_decode_sequence
import Theorems.Thm_BitcoinBlockV2_checkTransaction_iff
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

private theorem sumValues_nonneg : ∀ (os : List BitcoinSer.TxOut), (∀ o ∈ os, 0 ≤ o.nValue ∧ o.nValue ≤ MAX_MONEY) →
    0 ≤ BitcoinBlockV2.sumValues os
  | [], _ => by simp [sumValues]
  | o :: rest, h => by
    simp only [List.mem_cons, forall_eq_or_imp] at h
    simp only [sumValues]; have := sumValues_nonneg rest h.2; omega

private theorem outputsLoop_iff : ∀ (os : List BitcoinSer.TxOut) (acc : Int), 0 ≤ acc → acc ≤ MAX_MONEY →
    ((BitcoinBlockV2.outputsLoop os acc).isSome = true ↔
      (∀ o ∈ os, 0 ≤ o.nValue ∧ o.nValue ≤ MAX_MONEY) ∧ acc + BitcoinBlockV2.sumValues os ≤ MAX_MONEY)
  | [], acc, _, h2 => by simp [outputsLoop, sumValues, h2]
  | o :: rest, acc, h1, h2 => by
    simp only [outputsLoop, sumValues, List.mem_cons, forall_eq_or_imp]
    by_cases hn : o.nValue < 0
    · simp only [hn, ite_true, Option.isSome_none, Bool.false_eq_true, false_iff, not_and]
      intro h; omega
    · simp only [hn, ite_false]
      by_cases hm : MAX_MONEY < o.nValue
      · simp only [hm, ite_true, Option.isSome_none, Bool.false_eq_true, false_iff, not_and]
        intro h; omega
      · simp only [hm, ite_false]
        by_cases hr : moneyRange (acc + o.nValue) = true
        · simp only [hr, Bool.not_true, Bool.false_eq_true, ite_false]
          unfold moneyRange at hr; simp only [decide_eq_true_eq] at hr
          rw [outputsLoop_iff rest (acc + o.nValue) hr.1 hr.2]
          constructor
          · rintro ⟨ha, hb⟩; exact ⟨⟨⟨by omega, by omega⟩, ha⟩, by omega⟩
          · rintro ⟨⟨_, ha⟩, hb⟩; exact ⟨ha, by omega⟩
        · simp only [Bool.not_eq_true] at hr
          simp only [hr, Bool.not_false, ite_true, Option.isSome_none, Bool.false_eq_true, false_iff, not_and]
          unfold moneyRange at hr; simp only [decide_eq_false_iff_not] at hr
          rintro ⟨_, hrest⟩ hs
          have := sumValues_nonneg rest hrest
          omega

/-- `CheckBlock` characterized: the proof of work and the context-free block predicate. -/
theorem solution (b : BitcoinSer.Block) :
    BitcoinBlockV2.checkBlock b = true ↔ BitcoinBlockV2.checkHeaderPow b.header = true ∧ BitcoinBlockV2.BlockSpec b := by
  unfold checkBlock BlockSpec
  obtain ⟨hd, vtx⟩ := b
  cases vtx with
  | nil => simp
  | cons t rest =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff,
      List.all_eq_true, checkTransaction_iff, List.headD_cons, List.take_succ_cons, List.take_zero,
      List.mem_singleton, forall_eq, ne_eq, reduceCtorEq, not_false_eq_true, true_and, List.drop_succ_cons,
      List.drop_zero]
    constructor <;> intro h <;> simp_all
