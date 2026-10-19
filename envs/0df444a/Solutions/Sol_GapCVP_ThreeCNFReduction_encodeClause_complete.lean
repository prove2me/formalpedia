-- Prove2me | solution 1 for GapCVP.ThreeCNFReduction.encodeClause_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.096655+00:00
-- url     : https://prove2.me/submissions/faaaad52-957f-462d-9b7c-26437795e677

import Mathlib
import Definitions.Def_GapCVP
import Theorems.Thm_GapCVP_ThreeCNFReduction_gateList_complete

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open StateTransition (EvalsToInTime)
open GapCVP
open GapCVP.TraceGolf (oneStep rebound)
open GapCVP.ThreeCNFReduction
open GapCVP.CL
namespace GapCVP.ThreeCNFReduction
theorem _root_.solution {T S : ℕ}
    (clauses : List (Clause T S))
    (assignment : Variable T S → Bool)
    (clauseIndex : ℕ) (clause : Clause T S)
    (hclause : clauses[clauseIndex]? = some clause)
    (hsatisfied : CL.satisfiesClause assignment clause) :
    satisfies (liftAssignment clauses assignment)
      (encodeClause clauseIndex clause) := by
  simp only [GapCVP.CL.satisfiesClause, decide_eq_true_eq] at hsatisfied
  obtain ⟨literal, hmem, hvalue⟩ := hsatisfied
  have hany :
      (sortedElements clause).any
        (fun candidate => assignment candidate.1 == candidate.2) = true := by
    apply List.any_eq_true.mpr
    refine ⟨literal, (mem_sortedElements clause literal).mpr hmem, ?_⟩
    simpa using hvalue
  rw [encodeClause, satisfies_append, satisfies_append]
  refine ⟨⟨?_, gateList_complete clauses assignment clauseIndex clause
    hclause 0 (sortedElements clause) (by simp)⟩, ?_⟩
  · apply (paddedUnary_satisfied (liftAssignment clauses assignment) _).mpr
    simp only [GapCVP.literalSatisfied, decide_eq_true_eq]
    change liftAssignment clauses assignment
      (accumulatorVariable clauseIndex 0) = true
    rw [liftAssignment_accumulatorVariable clauses assignment
      clauseIndex 0 clause hclause]
    simpa using hany
  · apply (paddedUnary_satisfied (liftAssignment clauses assignment) _).mpr
    simp only [GapCVP.literalSatisfied, decide_eq_true_eq]
    change liftAssignment clauses assignment
      (accumulatorVariable clauseIndex (sortedElements clause).length) = false
    rw [liftAssignment_accumulatorVariable clauses assignment
      clauseIndex (sortedElements clause).length clause hclause]
    simp only [List.drop_length, List.any_nil]
end GapCVP.ThreeCNFReduction
