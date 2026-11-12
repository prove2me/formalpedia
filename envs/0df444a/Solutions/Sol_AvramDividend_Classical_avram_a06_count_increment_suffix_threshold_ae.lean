-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_count_increment_suffix_threshold_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T08:47:31.679609+00:00
-- url     : https://prove2.me/submissions/fa7e0188-90f5-420a-a080-48b77e1f41d2

import Mathlib.Probability.ConditionalProbability
import Theorems.Thm_AvramDividend_Classical_chat06_renewal_count_increment_residual_future_suffix_characterisation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- The pointwise renewal count-increment formula survives an almost-sure
    arrival-threshold hypothesis, uniformly over horizons and count indices. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (τ : ℕ → Ω → ℝ) (N : Ω → ℝ → ℕ)
    (hThreshold : ∀ᵐ ω ∂P, ∀ u k,
      k < N ω u ↔ (∑ i ∈ Finset.range (k + 1), τ i ω) ≤ u)
    (clock : ℝ) :
    ∀ᵐ ω ∂P, ∀ (v : ℝ) (k : ℕ), k < N ω (clock + v) - N ω clock ↔
        τ (N ω clock) ω -
          (clock - ∑ i ∈ Finset.range (N ω clock), τ i ω) +
          (∑ j ∈ Finset.range k, τ (N ω clock + 1 + j) ω) ≤ v := by
  filter_upwards [hThreshold] with ω hω
  intro v k
  let τ' : ℕ → Unit → ℝ := fun i _ => τ i ω
  let N' : Unit → ℝ → ℕ := fun _ u => N ω u
  have h' : ∀ z : Unit, ∀ u j,
      j < N' z u ↔ (∑ i ∈ Finset.range (j + 1), τ' i z) ≤ u := by
    intro z u j
    exact hω u j
  simpa only [τ', N'] using
    (AvramDividend.Classical.chat06_renewal_count_increment_residual_future_suffix_characterisation
      τ' N' h' () clock v k)