-- Prove2me | solution 1 for AvramDividend.Classical.chat06_nonnegative_wait_arrival_sums_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T17:56:35.93235+00:00
-- url     : https://prove2.me/submissions/5fefb6ca-6bfc-4249-bd29-472e9ddea79f

import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Cumulative arrival sums grow monotonically when all waiting
times are nonnegative, including the initial indexed arrival. -/
theorem solution
    (τ : ℕ → ℝ) (hτ : ∀ i, 0 ≤ τ i) :
    Monotone (fun n : ℕ => ∑ i ∈ Finset.range (n + 1), τ i) := by
  apply monotone_nat_of_le_succ
  intro n
  calc
    (∑ i ∈ Finset.range (n + 1), τ i) ≤
        (∑ i ∈ Finset.range (n + 1), τ i) + τ (n + 1) :=
      le_add_of_nonneg_right (hτ (n + 1))
    _ = ∑ i ∈ Finset.range ((n + 1) + 1), τ i :=
      (Finset.sum_range_succ τ (n + 1)).symm
