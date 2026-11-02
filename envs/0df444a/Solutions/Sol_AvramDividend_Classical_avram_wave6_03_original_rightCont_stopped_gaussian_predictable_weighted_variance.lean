-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_gaussian_predictable_weighted_variance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T20:56:36.408728+00:00
-- url     : https://prove2.me/submissions/9b14a172-05fb-43d8-b476-4f2ab63fd124

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_square_factor
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_exact_variance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (H : Ω → ℝ)
    (hH : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] H)
    (hHglobal : Measurable H) :
    (∫ ω, H ω *
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2 ∂P) =
    (∫ ω, H ω ∂P) * ((h : ℝ) * X.σ ^ 2) := by
  rw [avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_square_factor X hν τ hτ T hbounded h H hH hHglobal]
  exact congrArg (fun r : ℝ => (∫ ω, H ω ∂P) * r)
    (avram_wave6_03_original_rightCont_stopped_gaussian_exact_variance
      X hν τ (isStoppingTime_withTop_of_le_events τ hτ) T hbounded h)
