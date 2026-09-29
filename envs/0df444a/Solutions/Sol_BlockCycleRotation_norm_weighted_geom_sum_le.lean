-- Prove2me | solution 1 for BlockCycleRotation.norm_weighted_geom_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:17:11.71128+00:00
-- url     : https://prove2.me/submissions/716113de-343a-4290-b034-2c3fdb6e756d

import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_norm_geom_sum_le
import Mathlib

open Real Finset

namespace BlockCycleRotation

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

end BlockCycleRotation

open BlockCycleRotation in
/-- **Observation 15, weighted sum.**  For `0 < |θ| ≤ π`,
`‖∑_{1 ≤ j < T} j · e(jθ)‖ ≤ (T - 1) · π / |θ|`.

Proved by the paper's double-counting argument: write `j` as the number of `B`
with `1 ≤ B ≤ j`, swap the order of summation, and apply the geometric bound to
each inner sum. -/
theorem solution {θ : ℝ} (h0 : θ ≠ 0) (h : |θ| ≤ π) (T : ℕ) :
    ‖∑ j ∈ Finset.Ico 1 T, (j : ℂ) * e θ ^ j‖ ≤ (T - 1 : ℕ) * (π / |θ|):= by
  have key : ∑ j ∈ Finset.Ico 1 T, (j : ℂ) * e θ ^ j
      = ∑ i ∈ Finset.Ico 1 T, ∑ j ∈ Finset.Ico i T, e θ ^ j := by
    rw [Finset.sum_Ico_Ico_comm 1 T (fun _ j => e θ ^ j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    simp
  rw [key]
  calc ‖∑ i ∈ Finset.Ico 1 T, ∑ j ∈ Finset.Ico i T, e θ ^ j‖
      ≤ ∑ i ∈ Finset.Ico 1 T, ‖∑ j ∈ Finset.Ico i T, e θ ^ j‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.Ico 1 T, (π / |θ|) :=
        Finset.sum_le_sum fun i _ => norm_geom_sum_le h0 h i T
    _ = (T - 1 : ℕ) * (π / |θ|) := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
