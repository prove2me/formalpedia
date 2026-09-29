-- Prove2me | solution 1 for CelestialHolography.mobius_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T19:53:14.218013+00:00
-- url     : https://prove2.me/submissions/08397377-b441-4dd7-8d76-5ec604c49ef4

import Mathlib
import Definitions.Def_CelestialHolography_LorentzMobius_Defs

set_option autoImplicit false

theorem celHol_affine_hasDerivAt (a b z : ℂ) :
    HasDerivAt (fun y : ℂ => a * y + b) a z := by
  simpa using ((hasDerivAt_id z).const_mul a).add_const b

theorem celHol_det_fin_two (M : Matrix.SpecialLinearGroup (Fin 2) ℂ) :
    M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
  have h := M.2
  rw [Matrix.det_fin_two] at h
  exact h

open CelestialHolography in
theorem solution (M : Matrix.SpecialLinearGroup (Fin 2) ℂ) (z : ℂ)
    (hz : M 1 0 * z + M 1 1 ≠ 0) :
    HasDerivAt (mobius M) (1 / (M 1 0 * z + M 1 1) ^ 2) z := by
  have h := (celHol_affine_hasDerivAt (M 0 0) (M 0 1) z).div
    (celHol_affine_hasDerivAt (M 1 0) (M 1 1) z) hz
  have hdet := celHol_det_fin_two M
  have hfun : mobius M = fun y : ℂ => (M 0 0 * y + M 0 1) / (M 1 0 * y + M 1 1) := by
    funext y
    rfl
  have h2 : HasDerivAt (fun y : ℂ => (M 0 0 * y + M 0 1) / (M 1 0 * y + M 1 1))
      ((M 0 0 * (M 1 0 * z + M 1 1) - (M 0 0 * z + M 0 1) * M 1 0) /
        (M 1 0 * z + M 1 1) ^ 2) z := h
  rw [hfun]
  refine h2.congr_deriv ?_
  rw [div_left_inj' (pow_ne_zero 2 hz)]
  linear_combination hdet
