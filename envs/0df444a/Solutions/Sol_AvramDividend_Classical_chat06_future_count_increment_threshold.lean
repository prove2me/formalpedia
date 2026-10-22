-- Prove2me | solution 1 for AvramDividend.Classical.chat06_future_count_increment_threshold
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T18:02:16.136292+00:00
-- url     : https://prove2.me/submissions/2844c812-4cbf-406a-85f3-e371967b6207

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The additional renewal arrivals counted after a deterministic clock
exceed m exactly when the residual wait and following m waits fit in t. -/
theorem solution
    (τ : ℕ → ℝ) (N : ℝ → ℕ)
    (hThreshold : ∀ u k,
      k < N u ↔ (∑ i ∈ Finset.range (k + 1), τ i) ≤ u)
    (clock t : ℝ) (n m : ℕ) :
    m < N (clock + t) - n ↔
      ((∑ i ∈ Finset.range (n + 1), τ i) - clock) +
        (∑ j ∈ Finset.range m, τ ((n + 1) + j)) ≤ t := by
  have hIndex : n + m + 1 = (n + 1) + m := by
    simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hSum :
      (∑ i ∈ Finset.range (n + m + 1), τ i) =
        (∑ i ∈ Finset.range (n + 1), τ i) +
          (∑ j ∈ Finset.range m, τ ((n + 1) + j)) := by
    simpa only [hIndex] using (Finset.sum_range_add τ (n + 1) m)
  have hCore :
      n + m < N (clock + t) ↔
        ((∑ i ∈ Finset.range (n + 1), τ i) - clock) +
          (∑ j ∈ Finset.range m, τ ((n + 1) + j)) ≤ t := by
    rw [hThreshold (clock + t) (n + m), hSum]
    constructor <;> intro h <;> linarith
  rw [Nat.lt_sub_iff_add_lt]
  simpa only [Nat.add_comm] using hCore
