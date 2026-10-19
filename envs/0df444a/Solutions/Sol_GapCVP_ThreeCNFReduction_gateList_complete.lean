-- Prove2me | solution 1 for GapCVP.ThreeCNFReduction.gateList_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.096655+00:00
-- url     : https://prove2.me/submissions/e09ba8a0-adcb-4b03-aaa8-717184ab3f90

import Mathlib
import Definitions.Def_GapCVP
import Theorems.Thm_GapCVP_ThreeCNFReduction_orGate_satisfied
import Theorems.Thm_GapCVP_ThreeCNFReduction_drop_succ_of_drop_cons

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
    (prefixIndex : ℕ)
    (literals : List (SignedLiteral T S))
    (hdrop : (sortedElements clause).drop prefixIndex = literals) :
    satisfies (liftAssignment clauses assignment)
      (gateList clauseIndex prefixIndex literals) := by
  induction literals generalizing prefixIndex with
  | nil => simp [gateList]
  | cons literal remaining ih =>
    have hnext := drop_succ_of_drop_cons
      (sortedElements clause) prefixIndex literal remaining hdrop
    rw [gateList, satisfies_append]
    refine ⟨?_, ih (prefixIndex + 1) hnext⟩
    apply (orGate_satisfied (liftAssignment clauses assignment)
      (sourceLiteral literal)
      (accumulatorLiteral clauseIndex (prefixIndex + 1) true)
      (accumulatorLiteral clauseIndex prefixIndex true)).mpr
    simp only [GapCVP.literalSatisfied, decide_eq_true_eq]
    change
      liftAssignment clauses assignment
          (accumulatorVariable clauseIndex prefixIndex) = true ↔
        liftAssignment clauses assignment
            (sourceVariable literal.1) = literal.2 ∨
          liftAssignment clauses assignment
            (accumulatorVariable clauseIndex (prefixIndex + 1)) = true
    rw [liftAssignment_accumulatorVariable clauses assignment
      clauseIndex prefixIndex clause hclause,
      liftAssignment_sourceVariable clauses assignment literal.1,
      liftAssignment_accumulatorVariable clauses assignment
        clauseIndex (prefixIndex + 1) clause hclause,
      hdrop, hnext]
    simp
end GapCVP.ThreeCNFReduction
