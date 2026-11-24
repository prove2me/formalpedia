-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.chi_nsmul_left
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T04:32:22.506134+00:00
-- url     : https://prove2.me/submissions/f2a93c8b-8b5b-478f-9dbb-562b995d8384

import Mathlib
variable {W V : Type*} [AddCommGroup W] [AddCommGroup V] [Module ℂ V]
variable {χ : W → W → ℂ} (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y)
  (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y') (hχ0 : ∀ t y, χ t y ≠ 0)
include hχl hχ0


theorem solution (k : ℕ) (t y : W) : χ (k • t) y = χ t y ^ k := by
  have hzero : χ 0 y = 1 := by
    have he : χ 0 y = χ 0 y * χ 0 y := by simpa only [add_zero] using hχl 0 0 y
    apply mul_left_cancel₀ (hχ0 0 y); simpa only [mul_one] using he.symm
  induction k with
  | zero => simp [hzero]
  | succ k ih => rw [succ_nsmul, hχl, ih, pow_succ]
