-- Prove2me | solution 1 for GapCVP.ThreeCNFReduction.encodeFormula_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.096655+00:00
-- url     : https://prove2.me/submissions/9607e1fd-55bf-4b49-b326-07792f461dd0

import Mathlib
import Definitions.Def_GapCVP
import Theorems.Thm_GapCVP_ThreeCNFReduction_encodeFormulaFrom_sound

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
    (assignment : ℕ → Bool)
    (hsatisfied : satisfies assignment (encodeFormula formula)) :
    satisfiesFormula (restrictAssignment assignment) formula := by
  simp only [GapCVP.CL.satisfiesFormula, decide_eq_true_eq]
  intro clause hclause
  exact encodeFormulaFrom_sound assignment 0 (sortedElements formula)
    hsatisfied clause ((mem_sortedElements formula clause).mpr hclause)
end GapCVP.ThreeCNFReduction
