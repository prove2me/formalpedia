-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gaussian14_original_stopped_two_weights_gaussian_bracket
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T14:54:27.231197+00:00
-- url     : https://prove2.me/submissions/2f58c3b3-0b10-4ba1-9934-9baf66b1da56

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_L2_isometry_eq

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- At the original bounded stopping time the Gaussian error between two
predictable coefficients has the exact sigma-squared bracket budget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s]
      {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (G H : Ω → ℝ)
    (hG : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] G)
    (hH : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] H)
    (hGglobal : Measurable G) (hHglobal : Measurable H) :
    (∫ ω, ((G ω - H ω) *
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c)) ^ 2 ∂P) =
    (∫ ω, (G ω - H ω) ^ 2 ∂P) * ((h : ℝ) * X.σ ^ 2) := by
  exact avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_L2_isometry_eq
    X hν τ hτ T hbounded h (fun ω => G ω - H ω)
    (hG.sub hH) (hGglobal.sub hHglobal)
