-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.highest_weight_ones_eq_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:18:22.0984+00:00
-- url     : https://prove2.me/submissions/b749f7e0-a2a9-4168-a1bf-b6df1874d985

import Definitions.Def_Formalism_PieriBlockIdeals_ExZTranslate
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Theorems.Thm_Formalism_CohomologicalDescent_LA_highest_weight_shift_eq_det_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LA
theorem _root_.solution (R : Type) [CommRing R] (r : ℕ) :
    hw R le_rfl (fun _ : Fin r => 1) = genericDet R r := by
  have h := highest_weight_shift_eq_det_mul R (fun _ : Fin r => 0)
  have h0 : hw R le_rfl (fun _ : Fin r => 0) = 1 := by simp [hw]
  simpa [h0] using h
end Formalism.CohomologicalDescent.LA
