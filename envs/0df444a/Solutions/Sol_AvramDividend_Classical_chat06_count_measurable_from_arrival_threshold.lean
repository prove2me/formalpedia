-- Prove2me | solution 1 for AvramDividend.Classical.chat06_count_measurable_from_arrival_threshold
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T07:27:42.119986+00:00
-- url     : https://prove2.me/submissions/eafa9138-ec5b-4b7b-8882-a8fc9559c8a1

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Pi

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- The renewal count is measurable at any fixed clock whenever its
strict upper-count level sets are described by finite arrival sums. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (τ : ℕ → Ω → ℝ)
    (hτ : ∀ i, Measurable (τ i))
    (N : Ω → ℝ → ℕ)
    (hThreshold : ∀ ω u k,
      k < N ω u ↔ (∑ i ∈ Finset.range (k + 1), τ i ω) ≤ u)
    (clock : ℝ) :
    Measurable (fun ω => N ω clock) := by
  apply measurable_of_Iic
  intro n
  have heq :
      (fun ω => N ω clock) ⁻¹' Iic n =
        {ω | clock < ∑ i ∈ Finset.range (n + 1), τ i ω} := by
    ext ω
    change N ω clock ≤ n ↔
      clock < ∑ i ∈ Finset.range (n + 1), τ i ω
    simpa only [not_lt, not_le] using
      not_congr (hThreshold ω clock n)
  rw [heq]
  exact (Finset.measurable_sum _ fun i _ => hτ i) measurableSet_Ioi
