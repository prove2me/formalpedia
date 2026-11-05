-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_uniform_grid_linear_rate_sum_real
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:45:29.498196+00:00
-- url     : https://prove2.me/submissions/71accead-24fe-4646-b92f-d12c6c24026c

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators

/-- The exact real triangular rate sum for the physical uniform-cell pair grid. -/
theorem solution (k : ℕ) (a : ℝ) :
    (∑ i : Fin (k + 1), (i.val : ℝ) * a ^ 2) =
      (k : ℝ) * ((k : ℝ) + 1) / 2 * a ^ 2 := by
  have hsum (j : ℕ) :
      (∑ i : Fin (j + 1), (i.val : ℝ)) =
        (j : ℝ) * ((j : ℝ) + 1) / 2 := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih]
      push_cast
      ring
  calc
    (∑ i : Fin (k + 1), (i.val : ℝ) * a ^ 2) =
        (∑ i : Fin (k + 1), (i.val : ℝ)) * a ^ 2 := by
      rw [Finset.sum_mul]
    _ = (k : ℝ) * ((k : ℝ) + 1) / 2 * a ^ 2 := by
      rw [hsum]
