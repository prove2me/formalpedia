-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_threshold_residual_strict_positive_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T09:11:02.464512+00:00
-- url     : https://prove2.me/submissions/130c884b-9920-4f78-b443-86940390ae81

import Mathlib.Probability.ConditionalProbability
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Finset
noncomputable section

/-- The next arrival exceeds the clock on every sample satisfying the
    exact renewal count-threshold identity. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (τ : ℕ → Ω → ℝ) (N : Ω → ℝ → ℕ)
    (hThreshold : ∀ᵐ ω ∂P, ∀ (u : ℝ) (k : ℕ),
      k < N ω u ↔ (∑ i ∈ Finset.range (k + 1), τ i ω) ≤ u)
    (s : ℝ) :
    ∀ᵐ ω ∂P,
      0 < τ (N ω s) ω -
        (s - ∑ i ∈ Finset.range (N ω s), τ i ω) := by
  filter_upwards [hThreshold] with ω hw
  have hnot : ¬ N ω s < N ω s := lt_irrefl _
  have hbound :
      ¬ (∑ i ∈ Finset.range (N ω s + 1), τ i ω) ≤ s := by
    intro h
    exact hnot ((hw s (N ω s)).mpr h)
  rw [Finset.sum_range_succ] at hbound
  push_neg at hbound
  linarith
