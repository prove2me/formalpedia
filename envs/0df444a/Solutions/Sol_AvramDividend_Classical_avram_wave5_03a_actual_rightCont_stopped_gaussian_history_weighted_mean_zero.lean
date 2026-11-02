-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T17:52:35.7212+00:00
-- url     : https://prove2.me/submissions/fcb3b475-9693-4493-acc8-36088d76db64

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stoppedSigma_indep_shifted_source
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_drift_centered_increment_mean_zero

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
    (h : ℝ≥0)
    (H : Ω → ℝ)
    (hH : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] H)
    (hHglobal : Measurable H) :
    (∫ ω, H ω *
       (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ∂P) = 0 := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let F : Ω → (ℝ≥0 → ℝ) := fun ω t =>
    X.X (τ ω + t) ω - X.X (τ ω) ω
  let Y : Ω → ℝ := fun ω => F ω h - (h : ℝ) * X.c
  have hF : Measurable[MeasurableSpace.comap F inferInstance] F :=
    comap_measurable F
  have hEval : Measurable (fun f : ℝ≥0 → ℝ => f h) := measurable_pi_apply h
  have hY : Measurable[MeasurableSpace.comap F inferInstance] Y := by
    exact (hEval.comp hF).sub_const ((h : ℝ) * X.c)
  have hInd : Indep
      (MeasurableSpace.comap H inferInstance)
      (MeasurableSpace.comap Y inferInstance) P :=
    indep_of_indep_of_le
      (by simpa only [F] using
        (avram_wave5_03a_actual_rightCont_stoppedSigma_indep_shifted_source X τ hτ))
      hH.comap_le hY.comap_le
  have hIndFun : IndepFun H Y P := hInd
  have hτStop :
      IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)) :=
    isStoppingTime_withTop_of_le_events τ hτ
  have hMem : MemLp Y 2 P := by
    change MemLp (fun ω =>
      X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) 2 P
    exact avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
      X hν τ hτStop T hbounded h
  have hMean : (∫ ω, Y ω ∂P) = 0 := by
    change (∫ ω,
      X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c ∂P) = 0
    exact avram_wave5_03a_actual_rightCont_stopped_gaussian_drift_centered_increment_mean_zero
      X hν τ hτStop T hbounded h
  change (∫ ω, H ω * Y ω ∂P) = 0
  have hFactor :
      (∫ ω, H ω * Y ω ∂P) =
        (∫ ω, H ω ∂P) * (∫ ω, Y ω ∂P) := by
    simpa only [Pi.mul_apply] using
      (IndepFun.integral_mul_eq_mul_integral hIndFun
        hHglobal.aestronglyMeasurable hMem.aestronglyMeasurable)
  rw [hFactor, hMean, mul_zero]
