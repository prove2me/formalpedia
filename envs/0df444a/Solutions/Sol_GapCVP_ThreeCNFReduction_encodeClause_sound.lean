-- Prove2me | solution 1 for GapCVP.ThreeCNFReduction.encodeClause_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:26.272914+00:00
-- url     : https://prove2.me/submissions/f5728095-7540-4692-bc27-43a51c6ebc2c

import Mathlib
import Definitions.Def_GapCVP
import Theorems.Thm_GapCVP_ThreeCNFReduction_gateList_sound

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
    (assignment : ℕ → Bool)
    (clauseIndex : ℕ) (clause : Clause T S)
    (hsatisfied : satisfies assignment
      (encodeClause clauseIndex clause)) :
    CL.satisfiesClause (restrictAssignment assignment) clause := by
  simp only [GapCVP.CL.satisfiesClause, decide_eq_true_eq]
  simp only [encodeClause, satisfies_append] at hsatisfied
  obtain ⟨⟨hfirst, hgates⟩, hlast⟩ := hsatisfied
  have hstart : assignment (accumulatorVariable clauseIndex 0) = true := by
    simpa only [GapCVP.literalSatisfied, accumulatorLiteral, decide_eq_true_eq] using
      (paddedUnary_satisfied assignment _).mp hfirst
  have hfinish : assignment
      (accumulatorVariable clauseIndex
        (0 + (sortedElements clause).length)) = false := by
    simpa [literalSatisfied, accumulatorLiteral] using
      (paddedUnary_satisfied assignment _).mp hlast
  obtain ⟨literal, hmem, hvalue⟩ :=
    gateList_sound assignment clauseIndex 0
      (sortedElements clause) hgates hstart hfinish
  exact ⟨literal, (mem_sortedElements clause literal).mp hmem, hvalue⟩
end GapCVP.ThreeCNFReduction
