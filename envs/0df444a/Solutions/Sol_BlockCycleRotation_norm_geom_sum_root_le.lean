-- Prove2me | solution 1 for BlockCycleRotation.norm_geom_sum_root_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:30:04.379569+00:00
-- url     : https://prove2.me/submissions/54c86d23-368a-496e-acd7-c38ff22a29dc

import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_e_root_ne_one
import Theorems.Thm_BlockCycleRotation_two_div_norm_le
import Mathlib

open Real Finset

namespace BlockCycleRotation

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

/-- **Observation 15, geometric sum.**  For `0 < |θ| ≤ π`,
`‖∑_{B ≤ j < T} e(jθ)‖ ≤ π / |θ|`.

This is the trivial bound: the sum telescopes to a quotient whose numerator has
norm at most `2`, and the denominator is bounded below by Jordan's inequality. -/
theorem norm_geom_sum_le_prime {θ : ℝ} (hne : e θ ≠ 1) (B T : ℕ) :
    ‖∑ j ∈ Finset.Ico B T, e θ ^ j‖ ≤ 2 / ‖e θ - 1‖ := by
  have hpos : 0 < ‖e θ - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  rcases le_or_gt B T with hBT | hBT
  · rw [geom_sum_Ico hne hBT, norm_div]
    have hnum : ‖e θ ^ T - e θ ^ B‖ ≤ 2 := by
      calc ‖e θ ^ T - e θ ^ B‖ ≤ ‖e θ ^ T‖ + ‖e θ ^ B‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_e_pow, norm_e_pow]; norm_num
    gcongr
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty, norm_zero]
    positivity

end BlockCycleRotation

open BlockCycleRotation in
/-- **The bound §4 uses.**  For `0 < m < a`,
`‖∑_{B ≤ j < T} e(2πmj/a)‖ ≤ a / (2 · min(m, a-m))`. -/
theorem solution {a m : ℕ} (h0 : 0 < m) (hma : m < a) (B T : ℕ) :
    ‖∑ j ∈ Finset.Ico B T, e (2 * π * m / a) ^ j‖
      ≤ (a : ℝ) / (2 * ((min m (a - m) : ℕ) : ℝ)):=
  (norm_geom_sum_le_prime (e_root_ne_one h0 hma) B T).trans (two_div_norm_le h0 hma)
