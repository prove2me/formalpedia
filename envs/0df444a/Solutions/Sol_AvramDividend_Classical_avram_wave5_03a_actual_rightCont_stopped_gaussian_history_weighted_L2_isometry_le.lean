-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_L2_isometry_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:43:52.274056+00:00
-- url     : https://prove2.me/submissions/b008678d-97d0-4503-9772-aa1d0c77b7f2

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

/-- True original Gaussian stopped martingale-difference cells obey an
    L² isometry bound weighted by the stopped-history coefficient energy. -/
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
    (∫ ω, (H ω *
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c)) ^ 2 ∂P) ≤
    (∫ ω, (H ω) ^ 2 ∂P) * ((h : ℝ) * X.σ ^ 2) := by
  classical
  have hHsq :
      Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
        (fun ω => (H ω) ^ 2) :=
    hH.pow_const 2
  have hHsqGlobal : Measurable (fun ω => (H ω) ^ 2) :=
    hHglobal.pow_const 2
  have hFactor :
      (∫ ω, (H ω) ^ 2 *
        (X.X (τ ω + h) ω - X.X (τ ω) ω -
          (h : ℝ) * X.c) ^ 2 ∂P) =
      (∫ ω, (H ω) ^ 2 ∂P) *
        (∫ ω, (X.X (τ ω + h) ω - X.X (τ ω) ω -
          (h : ℝ) * X.c) ^ 2 ∂P) :=
    avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_square_factor
      X hν τ hτ T hbounded h (fun ω => (H ω) ^ 2)
      hHsq hHsqGlobal
  have hStop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)) :=
    isStoppingTime_withTop_of_le_events τ hτ
  have hVar :
      (∫ ω, (X.X (τ ω + h) ω - X.X (τ ω) ω -
        (h : ℝ) * X.c) ^ 2 ∂P) ≤ (h : ℝ) * X.σ ^ 2 :=
    avram_wave5_03a_actual_rightCont_stopped_gaussian_real_variance_le
      X hν τ hStop T hbounded h
  calc
    (∫ ω, (H ω *
        (X.X (τ ω + h) ω - X.X (τ ω) ω -
          (h : ℝ) * X.c)) ^ 2 ∂P) =
      (∫ ω, (H ω) ^ 2 *
        (X.X (τ ω + h) ω - X.X (τ ω) ω -
          (h : ℝ) * X.c) ^ 2 ∂P) := by
      congr 1
      funext ω
      ring
    _ = (∫ ω, (H ω) ^ 2 ∂P) *
          (∫ ω, (X.X (τ ω + h) ω - X.X (τ ω) ω -
            (h : ℝ) * X.c) ^ 2 ∂P) := hFactor
    _ ≤ (∫ ω, (H ω) ^ 2 ∂P) *
          ((h : ℝ) * X.σ ^ 2) :=
      mul_le_mul_of_nonneg_left hVar
        (integral_nonneg (fun ω => sq_nonneg (H ω)))
