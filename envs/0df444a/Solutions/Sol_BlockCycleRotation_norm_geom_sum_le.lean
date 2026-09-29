-- Prove2me | solution 1 for BlockCycleRotation.norm_geom_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:16:51.42836+00:00
-- url     : https://prove2.me/submissions/7e6a17c7-40dc-4b3c-9dda-e00420096b69

import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_mul_abs_le_norm_e_sub_one
import Mathlib

open Real Finset

namespace BlockCycleRotation

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

theorem e_ne_one {θ : ℝ} (h0 : θ ≠ 0) (h : |θ| ≤ π) : e θ ≠ 1 := by
  intro hc
  have hpos : 0 < 2 / π * |θ| := by
    have : 0 < |θ| := abs_pos.2 h0
    have := Real.pi_pos
    positivity
  have hle := mul_abs_le_norm_e_sub_one h
  rw [hc, sub_self, norm_zero] at hle
  linarith

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
/-- **Observation 15, geometric sum.**  For `0 < |θ| ≤ π`,
`‖∑_{B ≤ j < T} e(jθ)‖ ≤ π / |θ|`.

This is the trivial bound: the sum telescopes to a quotient whose numerator has
norm at most `2`, and the denominator is bounded below by Jordan's inequality. -/
theorem solution {θ : ℝ} (h0 : θ ≠ 0) (h : |θ| ≤ π) (B T : ℕ) :
    ‖∑ j ∈ Finset.Ico B T, e θ ^ j‖ ≤ π / |θ|:= by
  have hpi := Real.pi_pos
  have hθpos : 0 < |θ| := abs_pos.2 h0
  have hden : 2 / π * |θ| ≤ ‖e θ - 1‖ := mul_abs_le_norm_e_sub_one h
  have hdenpos : 0 < ‖e θ - 1‖ := by
    have : 0 < 2 / π * |θ| := by positivity
    linarith
  refine (norm_geom_sum_le_prime (e_ne_one h0 h) B T).trans ?_
  rw [div_le_div_iff₀ hdenpos hθpos]
  have hstep : 2 * |θ| ≤ π * ‖e θ - 1‖ := by
    have hmul := mul_le_mul_of_nonneg_left hden hpi.le
    calc 2 * |θ| = π * (2 / π * |θ|) := by field_simp
      _ ≤ π * ‖e θ - 1‖ := hmul
  linarith
