-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_square_energy_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:43:44.932003+00:00
-- url     : https://prove2.me/submissions/57289a4f-7683-4a58-be7c-eac702cb54f7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_square_factor
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_real_variance_le

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Stopped-history quadratic energy is controlled by the source's Gaussian
    variance rate, without a detached Brownian representation. -/
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
    (hHglobal : Measurable H) (hHnonneg : ∀ ω, 0 ≤ H ω) :
    (∫ ω, H ω *
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2 ∂P) ≤
    (∫ ω, H ω ∂P) * ((h : ℝ) * X.σ ^ 2) := by
  classical
  have hFactor :
      (∫ ω, H ω *
        (X.X (τ ω + h) ω - X.X (τ ω) ω -
          (h : ℝ) * X.c) ^ 2 ∂P) =
      (∫ ω, H ω ∂P) *
        (∫ ω, (X.X (τ ω + h) ω - X.X (τ ω) ω -
          (h : ℝ) * X.c) ^ 2 ∂P) :=
    avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_square_factor
      X hν τ hτ T hbounded h H hH hHglobal
  have hStop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)) :=
    isStoppingTime_withTop_of_le_events τ hτ
  have hVar :
      (∫ ω, (X.X (τ ω + h) ω - X.X (τ ω) ω -
        (h : ℝ) * X.c) ^ 2 ∂P) ≤ (h : ℝ) * X.σ ^ 2 :=
    avram_wave5_03a_actual_rightCont_stopped_gaussian_real_variance_le
      X hν τ hStop T hbounded h
  rw [hFactor]
  exact mul_le_mul_of_nonneg_left hVar (integral_nonneg hHnonneg)
