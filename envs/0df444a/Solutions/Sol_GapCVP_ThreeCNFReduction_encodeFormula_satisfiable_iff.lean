-- Prove2me | solution 1 for GapCVP.ThreeCNFReduction.encodeFormula_satisfiable_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.096655+00:00
-- url     : https://prove2.me/submissions/dc693b75-28f7-4798-ba29-de22a723dd71

import Mathlib
import Definitions.Def_GapCVP
import Theorems.Thm_GapCVP_ThreeCNFReduction_threeCNFSatisfiable_iff
import Theorems.Thm_GapCVP_ThreeCNFReduction_encodeFormula_allDistinct
import Theorems.Thm_GapCVP_ThreeCNFReduction_encodeFormula_sound
import Theorems.Thm_GapCVP_ThreeCNFReduction_encodeFormula_complete

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
    (formula : Formula T S) :
    threeCNFSatisfiable (encodeFormula formula) ↔
      ∃ assignment : Variable T S → Bool,
        satisfiesFormula assignment formula := by
  rw [threeCNFSatisfiable_iff]
  constructor
  · rintro ⟨_, assignment, hsatisfied⟩
    exact ⟨restrictAssignment assignment,
      encodeFormula_sound formula assignment hsatisfied⟩
  · rintro ⟨assignment, hsatisfied⟩
    exact ⟨encodeFormula_allDistinct formula,
      liftAssignment (sortedElements formula) assignment,
      encodeFormula_complete formula assignment hsatisfied⟩
end GapCVP.ThreeCNFReduction
