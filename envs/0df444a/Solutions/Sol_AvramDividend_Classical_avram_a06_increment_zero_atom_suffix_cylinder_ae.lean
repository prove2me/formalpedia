-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_increment_zero_atom_suffix_cylinder_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T11:56:48.424328+00:00
-- url     : https://prove2.me/submissions/f3756349-8ceb-4683-b142-9ac79dffcc99

import Mathlib.Probability.ConditionalProbability
import Theorems.Thm_AvramDividend_Classical_avram_a06_count_increment_suffix_threshold_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

/-- Zero new arrivals iff the residual wait exceeds the horizon. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (τ : ℕ → Ω → ℝ) (N : Ω → ℝ → ℕ)
    (hThreshold : ∀ᵐ ω ∂P, ∀ u k,
      k < N ω u ↔ (∑ i ∈ Finset.range (k + 1), τ i ω) ≤ u)
    (clock : ℝ) :
    ∀ᵐ ω ∂P, ∀ v : ℝ,
      N ω (clock + v) - N ω clock = 0 ↔
        v < τ (N ω clock) ω -
          (clock - ∑ i ∈ Finset.range (N ω clock), τ i ω) := by
  filter_upwards [
    AvramDividend.Classical.avram_a06_count_increment_suffix_threshold_ae
      P τ N hThreshold clock] with ω hω
  intro v
  have h := hω v 0
  constructor
  · intro heq
    have hn : ¬ (0 < N ω (clock + v) - N ω clock) := by omega
    have hn' : ¬ (τ (N ω clock) ω -
        (clock - ∑ i ∈ Finset.range (N ω clock), τ i ω) +
        (∑ j ∈ Finset.range 0, τ (N ω clock + 1 + j) ω) ≤ v) := by
      intro hx
      exact hn (h.mpr hx)
    simpa using lt_of_not_ge hn'
  · intro hv
    have hnot : ¬ (0 < N ω (clock + v) - N ω clock) := by
      intro hc
      have hle := h.mp hc
      simp only [Finset.sum_range_zero, add_zero] at hle
      exact (not_le_of_gt hv) hle
    omega
