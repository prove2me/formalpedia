-- Prove2me | solution 1 for AvramDividend.Classical.chat06_exact_count_cylinder_from_arrival_threshold
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T06:28:28.215281+00:00
-- url     : https://prove2.me/submissions/b45bfea6-5a02-453a-af46-120a913a5451

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Real.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Exact renewal count cylinders follow from the arrival-threshold
characterisation at every nonnegative deterministic observation time. -/
theorem solution
    (τ : ℕ → ℝ) (N : ℝ → ℕ)
    (hThreshold : ∀ u k,
      k < N u ↔ (∑ i ∈ Finset.range (k + 1), τ i) ≤ u)
    (clock : ℝ) (hclock : 0 ≤ clock) (n : ℕ) :
    N clock = n ↔
      (∑ i ∈ Finset.range n, τ i) ≤ clock ∧
        clock < ∑ i ∈ Finset.range (n + 1), τ i := by
  cases n with
  | zero =>
    constructor
    · intro hn
      have hnot : ¬ (0 : ℕ) < N clock := by
        rw [hn]
        exact Nat.lt_irrefl 0
      constructor
      · simpa using hclock
      · apply lt_of_not_ge
        intro hLe
        exact hnot ((hThreshold clock 0).mpr hLe)
    · rintro ⟨_, hUpper⟩
      have hnot : ¬ (0 : ℕ) < N clock := by
        intro hpos
        exact (not_le_of_gt hUpper) ((hThreshold clock 0).mp hpos)
      exact Nat.le_zero.mp (Nat.le_of_not_gt hnot)
  | succ k =>
    constructor
    · intro hn
      have hk : k < N clock := by
        rw [hn]
        exact Nat.lt_succ_self k
      have hnot : ¬ k + 1 < N clock := by
        rw [hn]
        exact Nat.lt_irrefl _
      constructor
      · exact (hThreshold clock k).mp hk
      · apply lt_of_not_ge
        intro hLe
        exact hnot ((hThreshold clock (k + 1)).mpr hLe)
    · rintro ⟨hLo, hHi⟩
      have hk : k < N clock := (hThreshold clock k).mpr hLo
      have hnot : ¬ k + 1 < N clock := by
        intro h
        exact (not_le_of_gt hHi) ((hThreshold clock (k + 1)).mp h)
      exact Nat.le_antisymm (Nat.le_of_not_gt hnot)
        (Nat.succ_le_of_lt hk)
