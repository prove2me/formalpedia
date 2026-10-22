-- Prove2me | solution 1 for AvramDividend.Classical.chat06_selected_future_count_increment_event
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T20:29:22.518892+00:00
-- url     : https://prove2.me/submissions/840fbab0-5f1a-4c22-89c9-fe75c022d957

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Pointwise count-increment thresholds remain exact when the observed
renewal count n is selected randomly from each sample path. -/
theorem solution
    {Ω : Type*} (τ : Ω → ℕ → ℝ) (N : Ω → ℝ → ℕ)
    (hThreshold : ∀ ω u k,
      k < N ω u ↔ (∑ i ∈ Finset.range (k + 1), τ ω i) ≤ u)
    (clock t : ℝ) (m : ℕ) :
    {ω : Ω | m < N ω (clock + t) - N ω clock} =
      {ω : Ω |
        ((∑ i ∈ Finset.range (N ω clock + 1), τ ω i) - clock) +
          (∑ j ∈ Finset.range m, τ ω ((N ω clock + 1) + j)) ≤ t} := by
  ext ω
  have hIndex :
      N ω clock + m + 1 = (N ω clock + 1) + m := by
    simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hSum :
      (∑ i ∈ Finset.range (N ω clock + m + 1), τ ω i) =
        (∑ i ∈ Finset.range (N ω clock + 1), τ ω i) +
          (∑ j ∈ Finset.range m, τ ω ((N ω clock + 1) + j)) := by
    simpa only [hIndex] using
      (Finset.sum_range_add (τ ω) (N ω clock + 1) m)
  have hCore :
      N ω clock + m < N ω (clock + t) ↔
        ((∑ i ∈ Finset.range (N ω clock + 1), τ ω i) - clock) +
          (∑ j ∈ Finset.range m, τ ω ((N ω clock + 1) + j)) ≤ t := by
    rw [hThreshold ω (clock + t) (N ω clock + m), hSum]
    constructor <;> intro h <;> linarith
  change (m < N ω (clock + t) - N ω clock) ↔
    ((∑ i ∈ Finset.range (N ω clock + 1), τ ω i) - clock) +
      (∑ j ∈ Finset.range m, τ ω ((N ω clock + 1) + j)) ≤ t
  rw [Nat.lt_sub_iff_add_lt]
  simpa only [Nat.add_comm] using hCore
