-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.chi_zero_left
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T04:32:12.166517+00:00
-- url     : https://prove2.me/submissions/b41f9e4d-75f9-4580-88e8-f8b386800eb3

import Mathlib
variable {W V : Type*} [AddCommGroup W] [AddCommGroup V] [Module ℂ V]
variable {χ : W → W → ℂ} (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y)
  (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y') (hχ0 : ∀ t y, χ t y ≠ 0)
include hχl hχ0


theorem solution (y : W) : χ 0 y = 1 := by
  have he : χ 0 y = χ 0 y * χ 0 y := by simpa only [add_zero] using hχl 0 0 y
  apply mul_left_cancel₀ (hχ0 0 y); simpa only [mul_one] using he.symm
