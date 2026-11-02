-- Prove2me | solution 2 for AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_quadratic_energy_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T21:06:06.339752+00:00
-- url     : https://prove2.me/submissions/370bf43e-65cb-4aa2-8c15-37ad404d877e

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_square_factor
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_exact_variance
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_predictable_weighted_variance

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
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s]
      {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (H : Ω → ℝ)
    (hH : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] H)
    (hHglobal : Measurable H) :
    (∫ ω, H ω *
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2 ∂P) =
      (∫ ω, H ω ∂P) * ((h : ℝ) * X.σ ^ 2) := by
  exact avram_wave6_03_original_rightCont_stopped_gaussian_predictable_weighted_variance
    X hν τ hτ T hbounded h H hH hHglobal
