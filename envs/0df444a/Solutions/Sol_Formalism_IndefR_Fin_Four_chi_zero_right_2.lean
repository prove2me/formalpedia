-- Prove2me | solution 2 for Formalism.IndefR.Fin.Four.chi_zero_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:36:41.896005+00:00
-- url     : https://prove2.me/submissions/1ee9e168-6bcb-4784-9699-413ae134ef33

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulSubMulLe
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourModel

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
include hχr hχ0
namespace Formalism.IndefR.Fin.Four
theorem _root_.solution (t : W) : χ t 0 = 1 := by
  have h := hχr t 0 0
  rw [add_zero] at h
  exact mul_left_cancel₀ (hχ0 t 0) (by rw [mul_one, ← h])
end Formalism.IndefR.Fin.Four
