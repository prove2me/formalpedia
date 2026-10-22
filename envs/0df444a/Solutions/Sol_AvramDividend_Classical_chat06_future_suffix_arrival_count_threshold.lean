-- Prove2me | solution 1 for AvramDividend.Classical.chat06_future_suffix_arrival_count_threshold
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T18:02:07.087168+00:00
-- url     : https://prove2.me/submissions/115c7c4d-9dba-4dfa-ba15-8046ba4e5ded

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The mth future arrival after index n has occurred by clock+t
precisely when the residual wait plus the following m waits is at most t. -/
theorem solution
    (τ : ℕ → ℝ) (N : ℝ → ℕ)
    (hThreshold : ∀ u k,
      k < N u ↔ (∑ i ∈ Finset.range (k + 1), τ i) ≤ u)
    (clock t : ℝ) (n m : ℕ) :
    n + m < N (clock + t) ↔
      ((∑ i ∈ Finset.range (n + 1), τ i) - clock) +
        (∑ j ∈ Finset.range m, τ ((n + 1) + j)) ≤ t := by
  have hIndex : n + m + 1 = (n + 1) + m := by
    simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hSum :
      (∑ i ∈ Finset.range (n + m + 1), τ i) =
        (∑ i ∈ Finset.range (n + 1), τ i) +
          (∑ j ∈ Finset.range m, τ ((n + 1) + j)) := by
    simpa only [hIndex] using (Finset.sum_range_add τ (n + 1) m)
  constructor
  · intro hn
    have hBefore :=
      (hThreshold (clock + t) (n + m)).mp hn
    rw [hSum] at hBefore
    linarith
  · intro ht
    apply (hThreshold (clock + t) (n + m)).mpr
    rw [hSum]
    linarith
