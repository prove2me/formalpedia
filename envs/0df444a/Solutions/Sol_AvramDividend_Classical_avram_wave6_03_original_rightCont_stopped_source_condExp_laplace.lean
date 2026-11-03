-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_source_condExp_laplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T07:36:42.666882+00:00
-- url     : https://prove2.me/submissions/07615bfd-cf6d-434f-9cc9-de21c12ec6cb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stoppedSigma_indep_shifted_source
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_levy_wholePath_measurable
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_increment_exp_integrable
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_expectation_one
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_full_future_source_law

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    Integrable (fun ω => Real.exp
      (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω))) P ∧
    (P[(fun ω => Real.exp
      (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω))) |
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
        =ᵐ[P] (fun _ => Real.exp ((h : ℝ) * X.ψ θ))) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)) :=
    isStoppingTime_withTop_of_le_events τ hτ
  obtain ⟨Z, hZpath, -, -, -⟩ :=
    avram_wave5_04_source_rightCont_levy_lift X
  let R : Ω → (ℝ≥0 → ℝ) := fun ω t =>
    X.X (τ ω + t) ω - X.X (τ ω) ω
  let F : (ℝ≥0 → ℝ) → ℝ := fun r => Real.exp (θ * r h)
  let E : Ω → ℝ := fun ω => F (R ω)
  have hI : Integrable E P := by
    simpa only [E, F, R, hZpath] using
      (levy_bounded_stopping_increment_exp_integrable
        Z τ hτstop T hbounded h θ hθ)
  have hRmeas : Measurable R := by
    simpa only [R, hZpath] using
      (levy_finiteStopping_stoppedFuturePath_measurable Z τ hτstop)
  have hFmeas : Measurable F :=
    Real.measurable_exp.comp
      (measurable_const.mul (measurable_pi_apply h))
  have hEmeas : Measurable E := hFmeas.comp hRmeas
  have hRcomap :
      Measurable[MeasurableSpace.comap R inferInstance] R :=
    comap_measurable R
  have hEcomap : Measurable[MeasurableSpace.comap R inferInstance] E :=
    hFmeas.comp hRcomap
  have hIndR : Indep (MeasurableSpace.comap R inferInstance)
      hτstop.measurableSpace P := by
    simpa only [R, hτstop] using
      (avram_wave5_03a_actual_rightCont_stoppedSigma_indep_shifted_source
        X τ hτ).symm
  have hIndE : Indep (MeasurableSpace.comap E inferInstance)
      hτstop.measurableSpace P :=
    indep_of_indep_of_le hIndR hEcomap.comap_le le_rfl
  have hCE : P[E | hτstop.measurableSpace] =ᵐ[P]
      (fun _ => ∫ ω, E ω ∂P) :=
    condExp_indep_eq hEmeas.comap_le hτstop.measurableSpace_le
      (comap_measurable E).stronglyMeasurable hIndE
  have hPathLaw :
      Measure.map R P =
        Measure.map (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P := by
    simpa only [R] using
      (avram_wave6_03_original_rightCont_stopped_full_future_source_law
        X τ hτ)
  have hXmeas :
      Measurable (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) :=
    levy_wholePath_measurable X
  have hIntegralLaw :
      (∫ ω, E ω ∂P) = (∫ ω, Real.exp (θ * X.X h ω) ∂P) := by
    change (∫ ω, F (R ω) ∂P) =
      ∫ ω, F (fun t : ℝ≥0 => X.X t ω) ∂P
    calc
      (∫ ω, F (R ω) ∂P) =
          ∫ r, F r ∂(Measure.map R P) :=
        (integral_map hRmeas.aemeasurable hFmeas.stronglyMeasurable.aestronglyMeasurable).symm
      _ = ∫ r, F r ∂(Measure.map
            (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P) := by
        rw [hPathLaw]
      _ = ∫ ω, F (fun t : ℝ≥0 => X.X t ω) ∂P :=
        integral_map hXmeas.aemeasurable hFmeas.stronglyMeasurable.aestronglyMeasurable
  have hNorm :=
    levy_compensated_exponential_expectation_one X h θ hθ
  have hDetLap :
      (∫ ω, Real.exp (θ * X.X h ω) ∂P) =
        Real.exp ((h : ℝ) * X.ψ θ) := by
    have hEqFn : (fun ω => Real.exp (θ * X.X h ω)) =
        (fun ω => Real.exp (θ * X.X h ω -
          (h : ℝ) * X.ψ θ) * Real.exp ((h : ℝ) * X.ψ θ)) := by
      funext ω
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hEqFn, integral_mul_const, hNorm, one_mul]
  have hLap : (∫ ω, E ω ∂P) =
      Real.exp ((h : ℝ) * X.ψ θ) :=
    hIntegralLaw.trans hDetLap
  change Integrable E P ∧
    (P[E | hτstop.measurableSpace] =ᵐ[P]
      (fun _ => Real.exp ((h : ℝ) * X.ψ θ)))
  exact ⟨hI, by simpa only [hLap] using hCE⟩