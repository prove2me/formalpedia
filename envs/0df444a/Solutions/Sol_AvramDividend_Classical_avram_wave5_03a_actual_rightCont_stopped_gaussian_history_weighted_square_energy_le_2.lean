-- Prove2me | solution 2 for AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_square_energy_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:45:21.367187+00:00
-- url     : https://prove2.me/submissions/3f861784-9eff-40b9-a859-862608fbc074

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_square_factor
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_real_variance_le

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
    (hHglobal : Measurable H) (hHnonneg : ∀ ω, 0 ≤ H ω) :
    (∫ ω, H ω *
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2 ∂P) ≤
    (∫ ω, H ω ∂P) * ((h : ℝ) * X.σ ^ 2) := by
  classical
  have hτStop :
      IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)) :=
    isStoppingTime_withTop_of_le_events τ hτ
  have hFactor :=
    avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_square_factor
      X hν τ hτ T hbounded h H hH hHglobal
  have hVar :=
    avram_wave5_03a_actual_rightCont_stopped_gaussian_real_variance_le
      X hν τ hτStop T hbounded h
  have hWeight : 0 ≤ (∫ ω, H ω ∂P) :=
    integral_nonneg hHnonneg
  rw [hFactor]
  exact mul_le_mul_of_nonneg_left hVar hWeight
