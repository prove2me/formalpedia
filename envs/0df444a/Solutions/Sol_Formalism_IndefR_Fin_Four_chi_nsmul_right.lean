-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.chi_nsmul_right
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T04:32:52.948632+00:00
-- url     : https://prove2.me/submissions/58c368ec-be37-4caf-b8a8-e63eef5ca4b3

import Mathlib
variable {W V : Type*} [AddCommGroup W] [AddCommGroup V] [Module ℂ V]
variable {χ : W → W → ℂ} (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y)
  (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y') (hχ0 : ∀ t y, χ t y ≠ 0)
include hχr hχ0


theorem solution (k : ℕ) (t y : W) : χ t (k • y) = χ t y ^ k := by
  have hzero : χ t 0 = 1 := by
    have he : χ t 0 = χ t 0 * χ t 0 := by simpa only [add_zero] using hχr t 0 0
    apply mul_left_cancel₀ (hχ0 t 0); simpa only [mul_one] using he.symm
  induction k with
  | zero => simp [hzero]
  | succ k ih => rw [succ_nsmul, hχr, ih, pow_succ]
