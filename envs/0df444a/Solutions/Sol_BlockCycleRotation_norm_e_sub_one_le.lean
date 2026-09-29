-- Prove2me | solution 1 for BlockCycleRotation.norm_e_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:14:08.239186+00:00
-- url     : https://prove2.me/submissions/6bec4214-f64a-4d49-90d0-1124c9478027

import Definitions.Def_BlockCycleRotation_ExpSum
import Mathlib

open Real Finset

namespace BlockCycleRotation

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

/-- `‖e θ - 1‖² = 2 - 2 cos θ`. -/
theorem norm_e_sub_one_sq (θ : ℝ) : ‖e θ - 1‖ ^ 2 = 2 - 2 * Real.cos θ := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [e, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, sub_zero]
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- The half-angle identity `2 - 2 cos θ = 4 sin²(θ/2)`. -/
theorem two_sub_two_cos (θ : ℝ) : 2 - 2 * Real.cos θ = 4 * Real.sin (θ / 2) ^ 2 := by
  have h := Real.cos_two_mul (θ / 2)
  rw [show 2 * (θ / 2) = θ by ring] at h
  nlinarith [Real.sin_sq_add_cos_sq (θ / 2)]

end BlockCycleRotation

open BlockCycleRotation in
/-- The easy half of Observation 15: `‖e θ - 1‖ ≤ |θ|`. -/
theorem solution (θ : ℝ) : ‖e θ - 1‖ ≤ |θ|:= by
  have habs : |θ / 2| = |θ| / 2 := by rw [abs_div, abs_two]
  have hs : |Real.sin (θ / 2)| ≤ |θ| / 2 := by
    have h := Real.abs_sin_le_abs (x := θ / 2)
    rwa [habs] at h
  have hsq : ‖e θ - 1‖ ^ 2 ≤ |θ| ^ 2 := by
    rw [norm_e_sub_one_sq, two_sub_two_cos, ← sq_abs (Real.sin (θ / 2))]
    nlinarith [abs_nonneg (Real.sin (θ / 2)), abs_nonneg θ, hs]
  have h1 := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (abs_nonneg θ)] at h1
