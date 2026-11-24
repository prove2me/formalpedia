-- Prove2me | solution 1 for Formalism.IndefR.Tow.OrbStPf.pd_update
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:43:43.305801+00:00
-- url     : https://prove2.me/submissions/97fd42ed-1adb-417b-8903-eac6ca833d64

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_SobolevIteration_DifferentiableUpdate
import Theorems.Thm_Formalism_IndefR_Tow_OrbStPf_pds_nil
import Theorems.Thm_Formalism_IndefR_Tow_OrbStPf_pds_cons
import Theorems.Thm_Formalism_IndefR_Tow_OrbStPf_pd_eq_deriv
import Theorems.Thm_Formalism_IndefR_Tow_OrbStPf_update_add_single
import Theorems.Thm_Formalism_IndefR_Tow_OrbStPf_differentiable_update
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
theorem _root_.solution (i j : Fin N) (hij : i ≠ j) (s : ℝ) {g : (Fin N → ℝ) → H} (hg : Differentiable ℝ g) :
    pd i (fun r => g (Function.update r j s)) = fun r => pd i g (Function.update r j s) := by
  funext r
  rw [pd_eq_deriv i (f := fun r => g (Function.update r j s)) r
      ((hg.comp (differentiable_update j s)) r),
    pd_eq_deriv i _ (hg _)]
  congr 1
  funext t
  simp only [update_add_single hij]
end Formalism.IndefR.Tow.OrbStPf
