-- Prove2me | solution 1 for BlockCycleRotation.four_mul_min_div_le_norm
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:28:42.811701+00:00
-- url     : https://prove2.me/submissions/6cf0e3ea-404e-43fe-8feb-f629ec46f14b

import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_two_mul_min_div_le_sin
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

/-- `‖e θ - 1‖ = 2 |sin (θ/2)|`, the exact form of the chord length. -/
theorem norm_e_sub_one_eq (θ : ℝ) : ‖e θ - 1‖ = 2 * |Real.sin (θ / 2)| := by
  have hsq : ‖e θ - 1‖ ^ 2 = (2 * |Real.sin (θ / 2)|) ^ 2 := by
    rw [norm_e_sub_one_sq, two_sub_two_cos, mul_pow, sq_abs]
    ring
  have h := congrArg Real.sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at h

end BlockCycleRotation

open BlockCycleRotation in
/-- The chord length at a nontrivial `a`-th root of unity. -/
theorem solution {a m : ℕ} (h0 : 0 < m) (hma : m < a) :
    4 * ((min m (a - m) : ℕ) : ℝ) / (a : ℝ) ≤ ‖e (2 * π * m / a) - 1‖:= by
  have hapos : 0 < a := lt_trans h0 hma
  have ha : (0 : ℝ) < a := by exact_mod_cast hapos
  have hhalf : 2 * π * (m : ℝ) / a / 2 = π * (m : ℝ) / a := by ring
  rw [norm_e_sub_one_eq, hhalf]
  have hs := two_mul_min_div_le_sin h0 hma
  have hnn : (0 : ℝ) ≤ 2 * ((min m (a - m) : ℕ) : ℝ) / a := by positivity
  rw [abs_of_nonneg (le_trans hnn hs)]
  calc 4 * ((min m (a - m) : ℕ) : ℝ) / (a : ℝ)
      = 2 * (2 * ((min m (a - m) : ℕ) : ℝ) / (a : ℝ)) := by ring
    _ ≤ 2 * Real.sin (π * (m : ℝ) / a) := by linarith
