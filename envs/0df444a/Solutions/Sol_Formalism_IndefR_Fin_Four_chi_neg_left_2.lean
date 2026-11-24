-- Prove2me | solution 2 for Formalism.IndefR.Fin.Four.chi_neg_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:11.428559+00:00
-- url     : https://prove2.me/submissions/66e8e654-a317-4112-8593-c14899c2d09e

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulSubMulLe
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourModel
import Theorems.Thm_Formalism_IndefR_Fin_Four_chi_zero_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.Fin Formalism.IndefR.Fin.Four
variable {W V : Type*} [AddCommGroup W] [AddCommGroup V] [Module ℂ V]
variable {χ : W → W → ℂ} (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y)
  (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y') (hχ0 : ∀ t y, χ t y ≠ 0)
include hχl hχ0
namespace Formalism.IndefR.Fin.Four
theorem _root_.solution (t y : W) : χ (-t) y = (χ t y)⁻¹ := by
  have h : χ t y * χ (-t) y = 1 := by
    rw [← hχl, add_neg_cancel, chi_zero_left hχl hχ0]
  exact eq_inv_of_mul_eq_one_right h
end Formalism.IndefR.Fin.Four
