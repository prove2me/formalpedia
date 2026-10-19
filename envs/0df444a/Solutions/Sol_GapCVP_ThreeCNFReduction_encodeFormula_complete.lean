-- Prove2me | solution 1 for GapCVP.ThreeCNFReduction.encodeFormula_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.096655+00:00
-- url     : https://prove2.me/submissions/e5624b7b-6bc9-44e2-b044-f7bd1e06827c

import Mathlib
import Definitions.Def_GapCVP
import Theorems.Thm_GapCVP_ThreeCNFReduction_encodeFormulaFrom_complete

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
    (formula : Formula T S)
    (assignment : Variable T S → Bool)
    (hsatisfied : satisfiesFormula assignment formula) :
    satisfies (liftAssignment (sortedElements formula) assignment)
      (encodeFormula formula) := by
  have hsatisfaction := hsatisfied
  simp only [GapCVP.CL.satisfiesFormula, decide_eq_true_eq] at hsatisfaction
  apply encodeFormulaFrom_complete
    (sortedElements formula) assignment 0 (sortedElements formula) (by simp)
  intro clause hclause
  exact hsatisfaction clause ((mem_sortedElements formula clause).mp hclause)
end GapCVP.ThreeCNFReduction
