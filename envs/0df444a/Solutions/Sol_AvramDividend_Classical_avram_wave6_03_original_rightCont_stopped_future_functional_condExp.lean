-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_future_functional_condExp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T07:40:25.804247+00:00
-- url     : https://prove2.me/submissions/e969bab0-e526-4604-b064-2a328c6f3cc7

import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stoppedSigma_indep_shifted_source
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable

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
    (Z : (ℝ≥0 → ℝ) → ℝ) (hZmeas : Measurable Z)
    (hInt : Integrable (fun ω : Ω => Z (fun t : ℝ≥0 =>
      X.X (τ ω + t) ω - X.X (τ ω) ω)) P) :
    P[(fun ω : Ω => Z (fun t : ℝ≥0 =>
      X.X (τ ω + t) ω - X.X (τ ω) ω)) |
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
      =ᵐ[P] (fun _ => ∫ ω, Z (fun t : ℝ≥0 =>
        X.X (τ ω + t) ω - X.X (τ ω) ω) ∂P) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)) :=
    isStoppingTime_withTop_of_le_events τ hτ
  obtain ⟨Y, hYpath, -, -, -⟩ :=
    avram_wave5_04_source_rightCont_levy_lift X
  let R : Ω → (ℝ≥0 → ℝ) := fun ω t =>
    X.X (τ ω + t) ω - X.X (τ ω) ω
  let V : Ω → ℝ := fun ω => Z (R ω)
  have hRmeas : Measurable R := by
    simpa only [R, hYpath] using
      (levy_finiteStopping_stoppedFuturePath_measurable Y τ hτstop)
  have hVmeas : Measurable V := hZmeas.comp hRmeas
  have hRcomap :
      Measurable[MeasurableSpace.comap R inferInstance] R :=
    comap_measurable R
  have hVcomap : Measurable[MeasurableSpace.comap R inferInstance] V :=
    hZmeas.comp hRcomap
  have hIndR : Indep (MeasurableSpace.comap R inferInstance)
      hτstop.measurableSpace P := by
    simpa only [R, hτstop] using
      (avram_wave5_03a_actual_rightCont_stoppedSigma_indep_shifted_source
        X τ hτ).symm
  have hIndV : Indep (MeasurableSpace.comap V inferInstance)
      hτstop.measurableSpace P :=
    indep_of_indep_of_le hIndR hVcomap.comap_le le_rfl
  have hCE : P[V | hτstop.measurableSpace] =ᵐ[P]
      (fun _ => ∫ ω, V ω ∂P) :=
    condExp_indep_eq hVmeas.comap_le hτstop.measurableSpace_le
      (comap_measurable V).stronglyMeasurable hIndV
  exact hCE
