-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.chi_neg_left
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T04:32:32.946945+00:00
-- url     : https://prove2.me/submissions/afae57f2-8a88-4d4f-8a9a-b98d4576d7ba

import Mathlib
variable {W V : Type*} [AddCommGroup W] [AddCommGroup V] [Module ℂ V]
variable {χ : W → W → ℂ} (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y)
  (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y') (hχ0 : ∀ t y, χ t y ≠ 0)
include hχl hχ0


theorem solution (t y : W) : χ (-t) y = (χ t y)⁻¹ := by
  have hz : χ 0 y = 1 := by
    have he : χ 0 y = χ 0 y * χ 0 y := by simpa only [add_zero] using hχl 0 0 y
    apply mul_left_cancel₀ (hχ0 0 y); simpa only [mul_one] using he.symm
  have hp : χ (-t) y * χ t y = 1 := by rw [← hχl,neg_add_cancel,hz]
  apply mul_right_cancel₀ (hχ0 t y); simpa [hχ0] using hp
