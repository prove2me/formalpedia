-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_L2_isometry_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T21:00:48.427263+00:00
-- url     : https://prove2.me/submissions/a0236ed2-f5f1-42d5-9a84-9c3a6196d83a

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

/-- Exact true-source Gaussian quadratic isometry for a stopped-history weight. -/
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
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c)) ^ 2 ∂P) =
    (∫ ω, (H ω) ^ 2 ∂P) * ((h : ℝ) * X.σ ^ 2) := by
  classical
  have hτStop :
      IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)) :=
    isStoppingTime_withTop_of_le_events τ hτ
  have hHsq :
      Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
        (fun ω => (H ω) ^ 2) :=
    hH.pow_const 2
  have hHsqGlobal : Measurable (fun ω => (H ω) ^ 2) :=
    hHglobal.pow_const 2
  have hFactor :=
    avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_square_factor
      X hν τ hτ T hbounded h (fun ω => (H ω) ^ 2) hHsq hHsqGlobal
  have hVar :=
    avram_wave6_03_original_rightCont_stopped_gaussian_exact_variance
      X hν τ hτStop T hbounded h
  have hEq :
      (∫ ω, (H ω) ^ 2 *
        (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2 ∂P) =
      (∫ ω, (H ω) ^ 2 ∂P) * ((h : ℝ) * X.σ ^ 2) := by
    calc
      _ = (∫ ω, (H ω) ^ 2 ∂P) *
          (∫ ω, (X.X (τ ω + h) ω - X.X (τ ω) ω -
            (h : ℝ) * X.c) ^ 2 ∂P) := hFactor
      _ = _ := by rw [hVar]
  simpa only [mul_pow] using hEq
