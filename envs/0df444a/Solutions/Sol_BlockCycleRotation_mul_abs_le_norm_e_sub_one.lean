-- Prove2me | solution 1 for BlockCycleRotation.mul_abs_le_norm_e_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:14:08.151184+00:00
-- url     : https://prove2.me/submissions/d175bc74-fd80-41e3-a15a-26ad01b6b466

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
/-- **Jordan's inequality for the circle.**  The hard half of Observation 15:
for `|θ| ≤ π` we have `(2/π)|θ| ≤ ‖e θ - 1‖`.

This is the bi-Lipschitz comparison between the arc-length and Euclidean metrics
on the unit circle. -/
theorem solution {θ : ℝ} (h : |θ| ≤ π) : 2 / π * |θ| ≤ ‖e θ - 1‖:= by
  have hpi := Real.pi_pos
  have habs : |θ / 2| = |θ| / 2 := by rw [abs_div, abs_two]
  have hhalf : |θ / 2| ≤ π / 2 := by rw [habs]; linarith
  have hj : 2 / π * |θ / 2| ≤ |Real.sin (θ / 2)| := Real.mul_abs_le_abs_sin hhalf
  rw [habs] at hj
  -- `|θ| / π ≤ |sin (θ/2)|`
  have h2 : 2 / π * (|θ| / 2) = |θ| / π := by ring
  have hj' : |θ| / π ≤ |Real.sin (θ / 2)| := by rwa [h2] at hj
  have hsq : (2 / π * |θ|) ^ 2 ≤ ‖e θ - 1‖ ^ 2 := by
    rw [norm_e_sub_one_sq, two_sub_two_cos, ← sq_abs (Real.sin (θ / 2))]
    have hnn : 0 ≤ |θ| / π := by positivity
    have h3 : (2 / π * |θ|) ^ 2 = 4 * (|θ| / π) ^ 2 := by ring
    rw [h3]
    nlinarith [mul_self_le_mul_self hnn hj', hnn, abs_nonneg (Real.sin (θ / 2))]
  have h1 := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq (norm_nonneg _)] at h1
