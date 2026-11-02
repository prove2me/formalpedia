-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_square_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:30:09.382715+00:00
-- url     : https://prove2.me/submissions/a0121dbe-e316-48ca-b79e-653ff54aad73

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stoppedSigma_indep_shifted_source
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The squared genuine stopped Gaussian increment is independent of its
    original right-continuous stopped history. -/
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
    (∫ ω, H ω ∂P) *
      (∫ ω, (X.X (τ ω + h) ω - X.X (τ ω) ω -
        (h : ℝ) * X.c) ^ 2 ∂P) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let F : Ω → (ℝ≥0 → ℝ) := fun ω t =>
    X.X (τ ω + t) ω - X.X (τ ω) ω
  let Δ : Ω → ℝ := fun ω => F ω h
  let Y : Ω → ℝ := fun ω => Δ ω - (h : ℝ) * X.c
  let Z : Ω → ℝ := fun ω => (Y ω) ^ 2
  have hF : Measurable[MeasurableSpace.comap F inferInstance] F :=
    comap_measurable F
  have hEval : Measurable (fun f : ℝ≥0 → ℝ => f h) :=
    measurable_pi_apply h
  have hΔ : Measurable[MeasurableSpace.comap F inferInstance] Δ :=
    hEval.comp hF
  have hY : Measurable[MeasurableSpace.comap F inferInstance] Y :=
    hΔ.sub measurable_const
  have hZeq : Z = Y * Y := by
    funext ω
    simp only [Z, pow_two, Pi.mul_apply]
  have hZ : Measurable[MeasurableSpace.comap F inferInstance] Z := by
    rw [hZeq]
    exact hY.mul hY
  have hInd : IndepFun H Z P :=
    indep_of_indep_of_le
      (by simpa only [F] using
        (avram_wave5_03a_actual_rightCont_stoppedSigma_indep_shifted_source
          X τ hτ))
      hH.comap_le hZ.comap_le
  have hStop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)) :=
    isStoppingTime_withTop_of_le_events τ hτ
  have hMem : MemLp Y 2 P := by
    simpa only [Y, Δ, F] using
      avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
        X hν τ hStop T hbounded h
  have hZaesm : AEStronglyMeasurable Z P := by
    rw [hZeq]
    exact hMem.aestronglyMeasurable.mul hMem.aestronglyMeasurable
  change (∫ ω, H ω * Z ω ∂P) =
      (∫ ω, H ω ∂P) * (∫ ω, Z ω ∂P)
  simpa only [Pi.mul_apply] using
    (IndepFun.integral_mul_eq_mul_integral hInd
      hHglobal.aestronglyMeasurable hZaesm)
