-- Prove2me | solution 1 for AvramDividend.Classical.chat06_selected_count_increment_exact_positive_cylinder
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T06:37:02.239992+00:00
-- url     : https://prove2.me/submissions/76a4b801-0308-4e19-89f3-50f87135578b

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Real.Basic
import Theorems.Thm_AvramDividend_Classical_chat06_selected_future_count_increment_event

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- A strictly positive renewal-count increment has an exact cylinder:
the corresponding future arrival is before t and the next one is after t. -/
theorem solution
    {Ω : Type*} (τ : Ω → ℕ → ℝ) (N : Ω → ℝ → ℕ)
    (hThreshold : ∀ ω u k,
      k < N ω u ↔ (∑ i ∈ Finset.range (k + 1), τ ω i) ≤ u)
    (clock t : ℝ) (m : ℕ) :
    {ω : Ω | N ω (clock + t) - N ω clock = m + 1} =
      {ω : Ω |
        ((∑ i ∈ Finset.range (N ω clock + 1), τ ω i) - clock) +
          (∑ j ∈ Finset.range m, τ ω (N ω clock + 1 + j)) ≤ t ∧
        t < ((∑ i ∈ Finset.range (N ω clock + 1), τ ω i) - clock) +
          (∑ j ∈ Finset.range (m + 1), τ ω (N ω clock + 1 + j))} := by
  ext ω
  have hLow :=
    (Set.ext_iff.mp
      (AvramDividend.Classical.chat06_selected_future_count_increment_event
        τ N hThreshold clock t m)) ω
  have hHigh :=
    (Set.ext_iff.mp
      (AvramDividend.Classical.chat06_selected_future_count_increment_event
        τ N hThreshold clock t (m + 1))) ω
  change
    (m < N ω (clock + t) - N ω clock) ↔
      ((∑ i ∈ Finset.range (N ω clock + 1), τ ω i) - clock) +
        (∑ j ∈ Finset.range m, τ ω (N ω clock + 1 + j)) ≤ t
    at hLow
  change
    (m + 1 < N ω (clock + t) - N ω clock) ↔
      ((∑ i ∈ Finset.range (N ω clock + 1), τ ω i) - clock) +
        (∑ j ∈ Finset.range (m + 1), τ ω (N ω clock + 1 + j)) ≤ t
    at hHigh
  constructor
  · intro hn
    constructor
    · apply hLow.mp
      rw [hn]
      exact Nat.lt_succ_self m
    · apply lt_of_not_ge
      intro hle
      have hlt := hHigh.mpr hle
      rw [hn] at hlt
      exact Nat.lt_irrefl _ hlt
  · rintro ⟨hlo, hhi⟩
    have hlt := hLow.mpr hlo
    have hnot : ¬ m + 1 < N ω (clock + t) - N ω clock := by
      intro hx
      exact (not_le_of_gt hhi) (hHigh.mp hx)
    exact Nat.le_antisymm (Nat.le_of_not_gt hnot)
      (Nat.succ_le_of_lt hlt)
