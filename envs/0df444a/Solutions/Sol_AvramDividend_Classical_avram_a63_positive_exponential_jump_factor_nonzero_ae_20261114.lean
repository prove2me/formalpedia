-- Prove2me | solution 1 for AvramDividend.Classical.avram_a63_positive_exponential_jump_factor_nonzero_ae_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:34:41.365208+00:00
-- url     : https://prove2.me/submissions/2a1b5e92-b1d0-4be3-940f-cbeae8b25416

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Probability.ConditionalProbability
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

/-- No real exponential of a physical jump variable vanishes almost surely on a probability space. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (J : Ω → ℝ) (θ : ℝ) :
    ¬ ((fun ω => Real.exp (θ * J ω)) =ᵐ[P]
      fun _ => (0 : ℝ)) := by
  intro hZero
  have hFalse : ∀ᵐ ω ∂P, False := by
    filter_upwards [hZero] with ω hω
    exact (Real.exp_ne_zero _) hω
  obtain ⟨ω, hω⟩ := hFalse.exists
  exact hω
