-- Prove2me | solution 1 for DiazModulus.imag_axis_div_normalisation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T06:11:27.048144+00:00
-- url     : https://prove2.me/submissions/247dcd4a-f56b-45d4-9eb5-a6ed01a41764

import Mathlib

theorem solution :
    ∀ γ : ℂ, γ.re = 0 →
      γ / (((Real.pi : ℝ) : ℂ) * Complex.I) = ((((γ.im / Real.pi : ℝ))) : ℂ) := by
  intro γ hγ
  have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  rw [div_eq_iff (mul_ne_zero hpi hI)]
  apply Complex.ext
  · simp [hγ]
  · simp
