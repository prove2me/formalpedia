-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_quadratic_energy_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T21:04:02.665266+00:00
-- url     : https://prove2.me/submissions/cccb679f-6fa2-431f-ac31-60c911a9c598

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_square_factor
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_exact_variance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Exact Hessian-weighted stopped Gaussian energy on the original path. -/
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
  classical
  have hτStop :
      IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)) :=
    isStoppingTime_withTop_of_le_events τ hτ
  have hFactor :=
    avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_square_factor
      X hν τ hτ T hbounded h H hH hHglobal
  have hVar :=
    avram_wave6_03_original_rightCont_stopped_gaussian_exact_variance
      X hν τ hτStop T hbounded h
  calc
    (∫ ω, H ω *
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2 ∂P) =
      (∫ ω, H ω ∂P) *
        (∫ ω, (X.X (τ ω + h) ω - X.X (τ ω) ω -
          (h : ℝ) * X.c) ^ 2 ∂P) := hFactor
    _ = _ := by rw [hVar]
