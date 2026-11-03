-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_gaussian_condExp_mean_variance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T06:32:49.565897+00:00
-- url     : https://prove2.me/submissions/d488dc3a-8899-49f8-9c83-535a3ccba2c6

import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Tactic.NormNum
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stoppedSigma_indep_shifted_source
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_drift_centered_increment_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_drift_centered_increment_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_exact_variance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Actual original right-continuous stopped Gaussian increments have exact
first and second conditional moments on the stopped-history sigma algebra. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) :
    let Y : Ω → ℝ := fun ω =>
      X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
    Integrable Y P ∧
      (P[Y | (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
        =ᵐ[P] (fun _ => (0 : ℝ))) ∧
    Integrable (fun ω => Y ω ^ 2) P ∧
      (P[(fun ω => Y ω ^ 2) |
        (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
        =ᵐ[P] (fun _ => (h : ℝ) * X.σ ^ 2)) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let hτstop : IsStoppingTime 𝓕.rightCont
    (fun ω => (τ ω : WithTop ℝ≥0)) :=
      isStoppingTime_withTop_of_le_events τ hτ
  let Y : Ω → ℝ := fun ω =>
    X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
  have hYMem : MemLp Y 2 P :=
    avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
      X hν τ hτstop T hbounded h
  have hYI : Integrable Y P :=
    hYMem.integrable (by norm_num)
  have hYsqI : Integrable (fun ω => Y ω ^ 2) P :=
    (memLp_two_iff_integrable_sq hYMem.aestronglyMeasurable).mp hYMem
  have hMean : (∫ ω, Y ω ∂P) = 0 :=
    avram_wave5_03a_actual_rightCont_stopped_gaussian_drift_centered_increment_mean_zero
      X hν τ hτstop T hbounded h
  have hVariance : (∫ ω, Y ω ^ 2 ∂P) = (h : ℝ) * X.σ ^ 2 :=
    avram_wave6_03_original_rightCont_stopped_gaussian_exact_variance
      X hν τ hτstop T hbounded h
  have hYmeas : Measurable Y :=
    avram_wave5_03a_actual_rightCont_stopped_drift_centered_increment_measurable
      X τ hτstop h
  have hYsm : StronglyMeasurable Y := hYmeas.stronglyMeasurable
  have hYsqSm : StronglyMeasurable (fun ω => Y ω ^ 2) := by
    convert hYsm.mul hYsm using 1
    funext ω
    simp only [Pi.mul_apply, pow_two]
  let R : Ω → (ℝ≥0 → ℝ) := fun ω t =>
    X.X (τ ω + t) ω - X.X (τ ω) ω
  have hRcomap : Measurable[MeasurableSpace.comap R inferInstance] R :=
    comap_measurable R
  have hEval : Measurable[MeasurableSpace.comap R inferInstance]
      (fun ω => R ω h) :=
    (measurable_pi_apply h).comp hRcomap
  have hYcomap : Measurable[MeasurableSpace.comap R inferInstance] Y := by
    change Measurable[MeasurableSpace.comap R inferInstance]
      (fun ω => R ω h - (h : ℝ) * X.c)
    exact hEval.sub_const _
  have hIndR : Indep (MeasurableSpace.comap R inferInstance)
      hτstop.measurableSpace P := by
    simpa only [R, hτstop] using
      (avram_wave5_03a_actual_rightCont_stoppedSigma_indep_shifted_source
        X τ hτ).symm
  have hIndY : Indep (MeasurableSpace.comap Y inferInstance)
      hτstop.measurableSpace P :=
    indep_of_indep_of_le hIndR hYcomap.comap_le le_rfl
  have hYsqComap : Measurable[MeasurableSpace.comap Y inferInstance]
      (fun ω => Y ω ^ 2) := by
    convert (comap_measurable Y).mul (comap_measurable Y) using 1
    funext ω
    simp only [Pi.mul_apply, pow_two]
  have hIndSq : Indep (MeasurableSpace.comap (fun ω => Y ω ^ 2) inferInstance)
      hτstop.measurableSpace P :=
    indep_of_indep_of_le hIndY hYsqComap.comap_le le_rfl
  have hCE0 : P[Y | hτstop.measurableSpace] =ᵐ[P]
      (fun _ => ∫ ω, Y ω ∂P) :=
    condExp_indep_eq hYsm.measurable.comap_le
      hτstop.measurableSpace_le (comap_measurable Y).stronglyMeasurable hIndY
  have hCEsq : P[(fun ω => Y ω ^ 2) | hτstop.measurableSpace] =ᵐ[P]
      (fun _ => ∫ ω, Y ω ^ 2 ∂P) :=
    condExp_indep_eq hYsqSm.measurable.comap_le
      hτstop.measurableSpace_le
      (comap_measurable (fun ω => Y ω ^ 2)).stronglyMeasurable hIndSq
  change Integrable Y P ∧
    (P[Y | hτstop.measurableSpace] =ᵐ[P] (fun _ => (0 : ℝ))) ∧
    Integrable (fun ω => Y ω ^ 2) P ∧
    (P[(fun ω => Y ω ^ 2) | hτstop.measurableSpace]
      =ᵐ[P] (fun _ => (h : ℝ) * X.σ ^ 2))
  exact ⟨hYI, by simpa only [hMean] using hCE0,
    hYsqI, by simpa only [hVariance] using hCEsq⟩
