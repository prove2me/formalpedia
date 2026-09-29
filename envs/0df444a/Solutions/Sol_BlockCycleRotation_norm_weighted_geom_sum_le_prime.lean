-- Prove2me | solution 1 for BlockCycleRotation.norm_weighted_geom_sum_le_prime
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:16:51.637293+00:00
-- url     : https://prove2.me/submissions/ce7a0c25-f9d0-4be9-8d5f-c7c39d155b38

import Definitions.Def_BlockCycleRotation_ExpSum
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
/-- The weighted sum bound in terms of the chord length, with no restriction on
`θ`.  Proved by the paper's double-counting argument: write `j` as the number of
`B` with `1 ≤ B ≤ j`, swap the order of summation, and apply the geometric
bound to each inner sum. -/
theorem solution {θ : ℝ} (hne : e θ ≠ 1) (T : ℕ) :
    ‖∑ j ∈ Finset.Ico 1 T, (j : ℂ) * e θ ^ j‖ ≤ (T - 1 : ℕ) * (2 / ‖e θ - 1‖):= by
  have key : ∑ j ∈ Finset.Ico 1 T, (j : ℂ) * e θ ^ j
      = ∑ i ∈ Finset.Ico 1 T, ∑ j ∈ Finset.Ico i T, e θ ^ j := by
    rw [Finset.sum_Ico_Ico_comm 1 T (fun _ j => e θ ^ j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    simp
  rw [key]
  calc ‖∑ i ∈ Finset.Ico 1 T, ∑ j ∈ Finset.Ico i T, e θ ^ j‖
      ≤ ∑ i ∈ Finset.Ico 1 T, ‖∑ j ∈ Finset.Ico i T, e θ ^ j‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.Ico 1 T, (2 / ‖e θ - 1‖) :=
        Finset.sum_le_sum fun i _ => norm_geom_sum_le_prime hne i T
    _ = (T - 1 : ℕ) * (2 / ‖e θ - 1‖) := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
