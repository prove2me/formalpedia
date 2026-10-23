-- Prove2me | solution 1 for AvramDividend.Classical.chat06_selected_count_increment_zero_cylinder
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T06:37:05.484404+00:00
-- url     : https://prove2.me/submissions/48aa8a50-0dcf-4e34-a2ec-e5e144bb0fd3

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Real.Basic
import Theorems.Thm_AvramDividend_Classical_chat06_selected_future_count_increment_event

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- No claims occur in the interval exactly when its length is shorter
than the selected residual waiting time to the next claim. -/
theorem solution
    {Ω : Type*} (τ : Ω → ℕ → ℝ) (N : Ω → ℝ → ℕ)
    (hThreshold : ∀ ω u k,
      k < N ω u ↔ (∑ i ∈ Finset.range (k + 1), τ ω i) ≤ u)
    (clock t : ℝ) :
    {ω : Ω | N ω (clock + t) - N ω clock = 0} =
      {ω : Ω |
        t < ((∑ i ∈ Finset.range (N ω clock + 1), τ ω i) - clock) +
          (∑ j ∈ Finset.range 0, τ ω (N ω clock + 1 + j))} := by
  ext ω
  have hEvent :=
    (Set.ext_iff.mp
      (AvramDividend.Classical.chat06_selected_future_count_increment_event
        τ N hThreshold clock t 0)) ω
  change
    (0 < N ω (clock + t) - N ω clock) ↔
      ((∑ i ∈ Finset.range (N ω clock + 1), τ ω i) - clock) +
        (∑ j ∈ Finset.range 0, τ ω (N ω clock + 1 + j)) ≤ t
    at hEvent
  change
    (N ω (clock + t) - N ω clock = 0) ↔
      t < ((∑ i ∈ Finset.range (N ω clock + 1), τ ω i) - clock) +
        (∑ j ∈ Finset.range 0, τ ω (N ω clock + 1 + j))
  constructor
  · intro hz
    apply lt_of_not_ge
    intro hle
    have hpos := hEvent.mpr hle
    rw [hz] at hpos
    exact Nat.lt_irrefl _ hpos
  · intro hgt
    have hnot : ¬ (0 : ℕ) < N ω (clock + t) - N ω clock := by
      intro hpos
      exact (not_le_of_gt hgt) (hEvent.mp hpos)
    exact Nat.le_zero.mp (Nat.le_of_not_gt hnot)
