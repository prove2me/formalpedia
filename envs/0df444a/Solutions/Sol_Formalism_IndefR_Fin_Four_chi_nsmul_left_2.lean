-- Prove2me | solution 2 for Formalism.IndefR.Fin.Four.chi_nsmul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:51.759684+00:00
-- url     : https://prove2.me/submissions/ec6c235a-589e-420d-a5e0-ab085dd8593c

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
theorem _root_.solution (k : ℕ) (t y : W) : χ (k • t) y = χ t y ^ k := by
  induction k with
  | zero => rw [zero_smul, chi_zero_left hχl hχ0, pow_zero]
  | succ n ih => rw [succ_nsmul, hχl, ih, pow_succ]
end Formalism.IndefR.Fin.Four
