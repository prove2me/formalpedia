-- Prove2me | solution 1 for AvramDividend.Classical.chat06_selected_count_increment_residual_suffix_threshold
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T06:42:29.382732+00:00
-- url     : https://prove2.me/submissions/0738d48b-0c87-47c0-8072-5385109c89fe

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_chat06_selected_future_count_increment_event

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Renewal count-increment thresholds in the residual-wait coordinates
used by the accepted random-count residual/future-suffix product law. -/
theorem solution
    {Ω : Type*} (τ : Ω → ℕ → ℝ) (N : Ω → ℝ → ℕ)
    (hThreshold : ∀ ω u k,
      k < N ω u ↔ (∑ i ∈ Finset.range (k + 1), τ ω i) ≤ u)
    (clock t : ℝ) (m : ℕ) :
    {ω : Ω | m < N ω (clock + t) - N ω clock} =
      {ω : Ω |
        (τ ω (N ω clock) -
          (clock - ∑ i ∈ Finset.range (N ω clock), τ ω i)) +
          (∑ j ∈ Finset.range m, τ ω (N ω clock + 1 + j)) ≤ t} := by
  calc
    {ω : Ω | m < N ω (clock + t) - N ω clock} =
      {ω : Ω |
        ((∑ i ∈ Finset.range (N ω clock + 1), τ ω i) - clock) +
          (∑ j ∈ Finset.range m, τ ω (N ω clock + 1 + j)) ≤ t} :=
        AvramDividend.Classical.chat06_selected_future_count_increment_event
          τ N hThreshold clock t m
    _ = {ω : Ω |
        (τ ω (N ω clock) -
          (clock - ∑ i ∈ Finset.range (N ω clock), τ ω i)) +
          (∑ j ∈ Finset.range m, τ ω (N ω clock + 1 + j)) ≤ t} := by
      ext ω
      have hR :
          (∑ i ∈ Finset.range (N ω clock + 1), τ ω i) - clock =
            τ ω (N ω clock) -
              (clock - ∑ i ∈ Finset.range (N ω clock), τ ω i) := by
        rw [Finset.sum_range_succ]
        ring
      change
        ((∑ i ∈ Finset.range (N ω clock + 1), τ ω i) - clock) +
            (∑ j ∈ Finset.range m, τ ω (N ω clock + 1 + j)) ≤ t ↔
          (τ ω (N ω clock) -
            (clock - ∑ i ∈ Finset.range (N ω clock), τ ω i)) +
            (∑ j ∈ Finset.range m, τ ω (N ω clock + 1 + j)) ≤ t
      rw [hR]
