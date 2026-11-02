-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_actual_rightCont_isStoppingTime_gaussian_simple_integral_L2_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:06:24.543886+00:00
-- url     : https://prove2.me/submissions/b154fd66-162b-4c8d-bc92-61366e36035e

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_history_simple_integral_L2_mean_zero

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
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (H : Ω → ℝ)
    (hH : Measurable[hτ.measurableSpace] H)
    (K : ℝ) (hK : 0 ≤ K) (hHbound : ∀ ω, |H ω| ≤ K) :
    MemLp (fun ω =>
      H ω * (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c)) 2 P ∧
    (∫ ω, H ω *
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ∂P) = 0 := by
  classical
  have hτevents : ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s} := by
    intro s
    simpa only [WithTop.coe_le_coe] using hτ s
  have hH' :
      Measurable[(isStoppingTime_withTop_of_le_events τ hτevents).measurableSpace] H :=
    hH
  exact avram_wave5_03a_actual_rightCont_stopped_gaussian_history_simple_integral_L2_mean_zero
    X hν τ hτevents T hbounded h H hH' K hK hHbound
