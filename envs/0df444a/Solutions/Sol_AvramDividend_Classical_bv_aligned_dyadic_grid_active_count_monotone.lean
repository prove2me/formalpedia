-- Prove2me | solution 1 for AvramDividend.Classical.bv_aligned_dyadic_grid_active_count_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T13:45:16.428758+00:00
-- url     : https://prove2.me/submissions/0b6f25ff-ac15-4f05-8128-233d7baec14e

import Theorems.Thm_AvramDividend_Classical_bv_dyadic_active_count_refinement
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Finset
open scoped NNReal

/-- Nested dyadic schedules yield a nondecreasing active-increment count. -/
theorem solution (Y : ℝ≥0 → ℝ) (grid : ℕ → ℕ → ℝ≥0)
    (hRefine : ∀ n i : ℕ, grid (n + 1) (2 * i) = grid n i) :
    Monotone (fun n : ℕ =>
      ∑ i ∈ range (2 ^ n),
        ite (Y (grid n i) < Y (grid n (i + 1))) (1 : ℕ) 0) := by
  apply monotone_nat_of_le_succ
  intro n
  have h := AvramDividend.Classical.bv_dyadic_active_count_refinement
    (fun j => Y (grid (n + 1) j)) (2 ^ n)
  calc
    (∑ i ∈ range (2 ^ n),
      ite (Y (grid n i) < Y (grid n (i + 1))) (1 : ℕ) 0) =
      ∑ i ∈ range (2 ^ n),
        ite (Y (grid (n + 1) (2 * i)) <
          Y (grid (n + 1) (2 * i + 2))) (1 : ℕ) 0 := by
            apply sum_congr rfl
            intro i hi
            have ha := hRefine n i
            have hb := hRefine n (i + 1)
            have hr : 2 * (i + 1) = 2 * i + 2 := by omega
            rw [hr] at hb
            rw [ha, hb]
    _ ≤ ∑ i ∈ range (2 * 2 ^ n),
       ite (Y (grid (n + 1) i) <
         Y (grid (n + 1) (i + 1))) (1 : ℕ) 0 := h
    _ = ∑ i ∈ range (2 ^ (n + 1)),
       ite (Y (grid (n + 1) i) <
         Y (grid (n + 1) (i + 1))) (1 : ℕ) 0 := by
           rw [pow_succ, mul_comm]
