-- Prove2me | solution 1 for Formalism.IndefR.Tow.OrbStPf.differentiable_update
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:45.304367+00:00
-- url     : https://prove2.me/submissions/c076b6d7-bfae-43f8-b4fa-ab1e5b75d8d1

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_SobolevIteration_DifferentiableUpdate
import Theorems.Thm_Formalism_IndefR_Tow_OrbStPf_pds_nil
import Theorems.Thm_Formalism_IndefR_Tow_OrbStPf_pds_cons
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.IndefR.Tow.OrbStPf.pds_nil
attribute [local simp] Formalism.IndefR.Tow.OrbStPf.pds_cons

set_option autoImplicit false
noncomputable section
open scoped ContDiff
open Formalism Formalism.IndefR Formalism.IndefR.Tow Formalism.IndefR.Tow.OrbStPf
variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
namespace Formalism.IndefR.Tow.OrbStPf
theorem _root_.solution (j : Fin N) (s : ℝ) :
    Differentiable ℝ (fun r : Fin N → ℝ => Function.update r j s) := by
  refine differentiable_pi.2 fun k => ?_
  by_cases hk : k = j
  · subst hk
    simp
  · simpa [Function.update_of_ne hk] using
      (differentiable_apply k : Differentiable ℝ fun r : Fin N → ℝ => r k)
end Formalism.IndefR.Tow.OrbStPf
