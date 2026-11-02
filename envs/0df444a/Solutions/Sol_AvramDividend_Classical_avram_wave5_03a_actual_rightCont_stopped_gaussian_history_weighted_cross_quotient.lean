-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_cross_quotient
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T17:58:58.885511+00:00
-- url     : https://prove2.me/submissions/9415f125-ada5-4545-9e3a-01921a7cd447

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stoppedSigma_indep_shifted_source
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_source_rightCont_stopped_gaussian_cross_quotient
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_source_rightCont_stopped_gaussian_quotient_L2_centered

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
    (h : ℝ≥0) (θ η : ℝ) (hθ : 0 ≤ θ) (hη : 0 ≤ η)
    (H : Ω → ℝ)
    (hH : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] H)
    (hHglobal : Measurable H) :
    (∫ ω, H ω *
      ((Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
        (h : ℝ) * X.ψ θ) - 1) / θ) *
      ((Real.exp (η * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
        (h : ℝ) * X.ψ η) - 1) / η) ∂P) =
    (∫ ω, H ω ∂P) *
      ((Real.exp ((h : ℝ) * (X.σ ^ 2 * θ * η)) - 1) / (θ * η)) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let F : Ω → (ℝ≥0 → ℝ) := fun ω t =>
    X.X (τ ω + t) ω - X.X (τ ω) ω
  let Δ : Ω → ℝ := fun ω => F ω h
  let Z : ℝ → Ω → ℝ := fun ξ ω =>
    (Real.exp (ξ * Δ ω - (h : ℝ) * X.ψ ξ) - 1) / ξ
  let Y : Ω → ℝ := fun ω => Z θ ω * Z η ω
  have hF : Measurable[MeasurableSpace.comap F inferInstance] F := comap_measurable F
  have hEval : Measurable (fun f : ℝ≥0 → ℝ => f h) := measurable_pi_apply h
  have hΔ : Measurable[MeasurableSpace.comap F inferInstance] Δ := hEval.comp hF
  have hZ (ξ : ℝ) :
      Measurable[MeasurableSpace.comap F inferInstance] (Z ξ) :=
    ((((measurable_const.mul hΔ).sub measurable_const).exp.sub
      measurable_const).div_const ξ)
  have hY : Measurable[MeasurableSpace.comap F inferInstance] Y :=
    (hZ θ).mul (hZ η)
  have hIndFun : IndepFun H Y P :=
    indep_of_indep_of_le
      (by simpa only [F] using
        (avram_wave5_03a_actual_rightCont_stoppedSigma_indep_shifted_source X τ hτ))
      hH.comap_le hY.comap_le
  have hτStop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)) :=
    isStoppingTime_withTop_of_le_events τ hτ
  have hMem (ξ : ℝ) (hξ : 0 ≤ ξ) : MemLp (Z ξ) 2 P := by
    simpa only [Z, Δ, F] using
      (avram_wave5_03a_actual_source_rightCont_stopped_gaussian_quotient_L2_centered
        X hν τ hτStop T hbounded h ξ hξ).1
  have hYaesm : AEStronglyMeasurable Y P :=
    ((hMem θ hθ).aestronglyMeasurable.mul (hMem η hη).aestronglyMeasurable)
  have hCross : (∫ ω, Y ω ∂P) =
      (Real.exp ((h : ℝ) * (X.σ ^ 2 * θ * η)) - 1) / (θ * η) := by
    simpa only [Y, Z, Δ, F] using
      (avram_wave5_03a_actual_source_rightCont_stopped_gaussian_cross_quotient
        X hν τ hτStop T hbounded h θ η hθ hη)
  have hFactor : (∫ ω, H ω * Z θ ω * Z η ω ∂P) =
      (∫ ω, H ω ∂P) * (∫ ω, Y ω ∂P) := by
    simpa only [Pi.mul_apply, Y, mul_assoc] using
      (IndepFun.integral_mul_eq_mul_integral hIndFun
        hHglobal.aestronglyMeasurable hYaesm)
  change (∫ ω, H ω * Z θ ω * Z η ω ∂P) =
    (∫ ω, H ω ∂P) *
      ((Real.exp ((h : ℝ) * (X.σ ^ 2 * θ * η)) - 1) / (θ * η))
  rw [hFactor, hCross]
