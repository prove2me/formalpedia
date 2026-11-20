-- Prove2me | solution 1 for DeletionCode.ExceptionalPartnerCount.bad_record_of_not_separated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:06:47.928366+00:00
-- url     : https://prove2.me/submissions/c2d637f7-7d39-43fb-be9f-e7c4d9c323e6

import Definitions.Def_DeletionCode_AnchorRecords
import Definitions.Def_DeletionCode_TaggedAnchorCount
import Definitions.Def_DeletionCode_ExceptionalProbability
import Definitions.Def_DeletionCode_ExceptionalCountArithmetic
import Definitions.Def_DeletionCode_ExceptionalPartnerCount
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_matchedAnchor_le
import Theorems.Thm_DeletionCode_AnchorRecords_vector_edit_indices
import Theorems.Thm_DeletionCode_TraceSeparation_matchedAnchor_mono


set_option autoImplicit true
open DeletionCode DeletionCode.ExceptionalPartnerCount
open HeaderRecovery TaggedAnchorCount AlignmentTrace FiniteConflictGraph TraceEditData
open ExceptionalProbability ExceptionalCountArithmetic
open scoped BigOperators
namespace DeletionCode.ExceptionalPartnerCount
theorem _root_.solution {n r B : ℕ} (trace : Trace) (record : Record n r)
    (heq : packets record = AnchorRecords.encode trace) (hnot : ¬ Separated B trace) :
    Bad trace.matchedCount B record := by
  obtain ⟨e, he, ha⟩ := AnchorRecords.vector_edit_indices trace record.1 record.2 heq
  by_contra hbad
  apply hnot
  constructor
  · intro i hi
    let c : EditColumn trace := ⟨i, hi⟩
    have heq' := ha c
    have hl : ¬ (record.1 (e c)).val < B := fun h => hbad (Or.inl ⟨e c, h⟩)
    have hr : ¬ Nat.dist (record.1 (e c)).val trace.matchedCount < B :=
      fun h => hbad (Or.inr (Or.inl ⟨e c, h⟩))
    rw [heq'] at hl hr
    have hle := trace.matchedAnchor_le i.val
    change ¬ trace.matchedAnchor i.val < B at hl
    change ¬ Nat.dist (trace.matchedAnchor i.val) trace.matchedCount < B at hr
    unfold Nat.dist at hr
    constructor <;> omega
  · intro i j hi hj hij
    let c : EditColumn trace := ⟨i, hi⟩
    let d : EditColumn trace := ⟨j, hj⟩
    have hne : e c ≠ e d := by
      intro h
      have hv := congrArg (fun q : EditColumn trace => q.val.val) (he h)
      change i.val = j.val at hv
      omega
    have hp : ¬ Nat.dist (record.1 (e c)).val (record.1 (e d)).val < B :=
      fun h => hbad (Or.inr (Or.inr ⟨e c, e d, hne, h⟩))
    rw [ha c, ha d] at hp
    change ¬ Nat.dist (trace.matchedAnchor i.val) (trace.matchedAnchor j.val) < B at hp
    have hmono := TraceSeparation.matchedAnchor_mono trace (Nat.le_of_lt hij)
    unfold Nat.dist at hp
    omega
end DeletionCode.ExceptionalPartnerCount
