-- Prove2me | solution 1 for AvramDividend.Classical.chat06_observed_count_history_measurable_from_arrival_threshold
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T08:00:51.967996+00:00
-- url     : https://prove2.me/submissions/e2ac31df-9648-47d1-9c96-0701fc30c983

import Mathlib.MeasureTheory.Constructions.Pi
import Theorems.Thm_AvramDividend_Classical_chat06_count_measurable_from_arrival_threshold

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- Every observed renewal count history path up to a fixed clock
is measurable if its interarrival sequence is measurable and the
renewal count is characterised by its arrival thresholds. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (τ : ℕ → Ω → ℝ)
    (hτ : ∀ i, Measurable (τ i))
    (N : Ω → ℝ → ℕ)
    (hThreshold : ∀ ω u k,
      k < N ω u ↔ (∑ i ∈ Finset.range (k + 1), τ i ω) ≤ u)
    (clock : ℝ) :
    Measurable (fun ω : Ω => fun s : Set.Iic clock => N ω (s : ℝ)) := by
  exact measurable_pi_iff.mpr (fun s =>
    AvramDividend.Classical.chat06_count_measurable_from_arrival_threshold
      τ hτ N hThreshold (s : ℝ))
