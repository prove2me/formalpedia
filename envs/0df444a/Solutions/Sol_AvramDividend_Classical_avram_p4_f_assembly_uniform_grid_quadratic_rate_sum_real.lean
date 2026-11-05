-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_uniform_grid_quadratic_rate_sum_real
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T15:03:42.865348+00:00
-- url     : https://prove2.me/submissions/d6f92144-fc6c-4118-b469-ae72482cdec3

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators
noncomputable section

/-- The exact deterministic second-factorial cross-cell rate sum. -/
theorem solution
    (N : ℕ) (hN : 0 < N) (r : ℝ) :
    (∑ i ∈ Finset.range N,
      ((i : ℝ) * r / (N : ℝ)) * (r / (N : ℝ))) =
      (((N : ℝ) - 1) / (2 * (N : ℝ))) * r ^ 2 := by
  have hN0 : (N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hN)
  have hsum (k : ℕ) :
      (∑ i ∈ Finset.range k, (i : ℝ)) =
        (k : ℝ) * ((k : ℝ) - 1) / 2 := by
    induction k with
    | zero => norm_num
    | succ k ih =>
        rw [Finset.sum_range_succ, ih]
        push_cast
        ring
  calc
    (∑ i ∈ Finset.range N,
        ((i : ℝ) * r / (N : ℝ)) * (r / (N : ℝ))) =
      ∑ i ∈ Finset.range N, (i : ℝ) * (r / (N : ℝ)) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
    _ = (((N : ℝ) - 1) / (2 * (N : ℝ))) * r ^ 2 := by
      rw [← Finset.sum_mul, hsum N]
      field_simp [hN0]
