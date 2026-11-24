-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.chi_zero_right
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T04:32:43.148195+00:00
-- url     : https://prove2.me/submissions/67090031-d3f8-4419-82a4-b057e5da080a

import Mathlib
variable {W V : Type*} [AddCommGroup W] [AddCommGroup V] [Module ℂ V]
variable {χ : W → W → ℂ} (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y)
  (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y') (hχ0 : ∀ t y, χ t y ≠ 0)
include hχr hχ0


theorem solution (t : W) : χ t 0 = 1 := by
  have he : χ t 0 = χ t 0 * χ t 0 := by simpa only [add_zero] using hχr t 0 0
  apply mul_left_cancel₀ (hχ0 t 0); simpa only [mul_one] using he.symm
