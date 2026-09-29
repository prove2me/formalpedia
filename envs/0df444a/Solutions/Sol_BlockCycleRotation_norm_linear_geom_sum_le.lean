-- Prove2me | solution 1 for BlockCycleRotation.norm_linear_geom_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:36:51.710068+00:00
-- url     : https://prove2.me/submissions/0816e2a3-a473-4cff-828f-79ea0c65c306

import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_norm_weighted_geom_sum_le_prime
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

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

end BlockCycleRotation

open BlockCycleRotation in
/-- **The inner sum.**  A linear function twisted by a character, bounded by the
chord length. -/
theorem solution {θ : ℝ} (hne : e θ ≠ 1) (A B : ℂ) (T : ℕ) :
    ‖∑ b ∈ Finset.Ico 1 T, (A + B * b) * e θ ^ b‖
      ≤ (‖A‖ + ‖B‖ * (T - 1 : ℕ)) * (2 / ‖e θ - 1‖):= by
  have hsplit : ∑ b ∈ Finset.Ico 1 T, (A + B * b) * e θ ^ b
      = A * (∑ b ∈ Finset.Ico 1 T, e θ ^ b)
        + B * (∑ b ∈ Finset.Ico 1 T, (b : ℂ) * e θ ^ b) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [hsplit]
  have h1 := norm_geom_sum_le_prime hne 1 T
  have h2 := norm_weighted_geom_sum_le_prime hne T
  calc ‖A * (∑ b ∈ Finset.Ico 1 T, e θ ^ b)
        + B * (∑ b ∈ Finset.Ico 1 T, (b : ℂ) * e θ ^ b)‖
      ≤ ‖A * (∑ b ∈ Finset.Ico 1 T, e θ ^ b)‖
        + ‖B * (∑ b ∈ Finset.Ico 1 T, (b : ℂ) * e θ ^ b)‖ := norm_add_le _ _
    _ = ‖A‖ * ‖∑ b ∈ Finset.Ico 1 T, e θ ^ b‖
        + ‖B‖ * ‖∑ b ∈ Finset.Ico 1 T, (b : ℂ) * e θ ^ b‖ := by rw [norm_mul, norm_mul]
    _ ≤ ‖A‖ * (2 / ‖e θ - 1‖) + ‖B‖ * ((T - 1 : ℕ) * (2 / ‖e θ - 1‖)) := by gcongr
    _ = (‖A‖ + ‖B‖ * (T - 1 : ℕ)) * (2 / ‖e θ - 1‖) := by ring
