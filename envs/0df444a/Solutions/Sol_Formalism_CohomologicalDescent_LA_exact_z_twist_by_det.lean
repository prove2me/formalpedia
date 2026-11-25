-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.exact_z_twist_by_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:15:27.263034+00:00
-- url     : https://prove2.me/submissions/ef2cc770-1ce4-420d-85c5-952f1fc42a31

import Definitions.Def_Formalism_PieriBlockIdeals_ExZTranslate
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Theorems.Thm_Formalism_CohomologicalDescent_LA_incl_z_twist_by_det
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
theorem _root_.solution : ExZTwist := by
  unfold ExZTwist
  intro r ν c l hν hl
  have h : ∀ e, InclZ r r le_rfl (fun a => ν a + c) l e ↔ InclZ r r le_rfl ν l e :=
    fun e => incl_z_twist_by_det r ν c l e hν hl
  unfold exZ
  simp only [h]
end Formalism.CohomologicalDescent.LA
