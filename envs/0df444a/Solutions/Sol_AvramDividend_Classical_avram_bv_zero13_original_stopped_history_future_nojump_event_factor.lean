-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_zero13_original_stopped_history_future_nojump_event_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T23:56:16.640724+00:00
-- url     : https://prove2.me/submissions/49762c78-497b-4292-8699-25a96e067dc8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stoppedSigma_indep_shifted_source
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_stoppedHistory_event_measurable
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0)
    (A : Set Ω)
    (hA : MeasurableSet[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] A) :
    P (A ∩ {ω : Ω |
      ((T : ℝ) * X.drift -
        (X.X (τ ω + T) ω - X.X (τ ω) ω)) -
      (((0 : ℝ≥0) : ℝ) * X.drift -
        (X.X (τ ω + 0) ω - X.X (τ ω) ω)) = 0}) =
      P A * P {ω : Ω |
      ((T : ℝ) * X.drift -
        (X.X (τ ω + T) ω - X.X (τ ω) ω)) -
      (((0 : ℝ≥0) : ℝ) * X.drift -
        (X.X (τ ω + 0) ω - X.X (τ ω) ω)) = 0} := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let hstop := isStoppingTime_withTop_of_le_events τ hτ
  let F : Ω → (ℝ≥0 → ℝ) := fun ω t =>
    X.X (τ ω + t) ω - X.X (τ ω) ω
  let B : Set (ℝ≥0 → ℝ) := {g |
    ((T : ℝ) * X.drift - g T) -
      (((0 : ℝ≥0) : ℝ) * X.drift - g 0) = 0}
  have hB : MeasurableSet B := by
    have hMeas : Measurable (fun g : ℝ≥0 → ℝ =>
        ((T : ℝ) * X.drift - g T) -
          (((0 : ℝ≥0) : ℝ) * X.drift - g 0)) :=
      (measurable_const.sub (measurable_pi_apply T)).sub
        (measurable_const.sub (measurable_pi_apply 0))
    exact hMeas (measurableSet_singleton (0 : ℝ))
  have hF : Measurable F := by
    obtain ⟨Y, hYpath, -, -, -⟩ :=
      avram_wave5_04_source_rightCont_levy_lift X
    simpa only [F, hYpath] using
      (levy_finiteStopping_stoppedFuturePath_measurable Y τ hstop)
  have hIndep : Indep hstop.measurableSpace
      (MeasurableSpace.comap F inferInstance) P := by
    simpa only [F, hstop] using
      (avram_wave5_03a_actual_rightCont_stoppedSigma_indep_shifted_source X τ hτ)
  have hEvent : MeasurableSet[MeasurableSpace.comap F inferInstance]
      (F ⁻¹' B) := by
    exact (MeasurableSpace.measurableSet_comap).2 ⟨B, hB, rfl⟩
  have hEventAmbient : MeasurableSet (F ⁻¹' B) := hF hB
  have hAstopped : ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s]
        (A ∩ {ω : Ω | τ ω ≤ s}) := by
    intro s
    have hs := ((hstop.measurableSet A).mp hA).2 s
    simpa only [WithTop.coe_le_coe] using hs
  have hAmbient : MeasurableSet A := by
    exact stoppedHistory_event_measurable τ A hAstopped
  have hIndepSet : IndepSet A (F ⁻¹' B) P :=
    (indep_iff_forall_indepSet P).1 hIndep A (F ⁻¹' B) hA hEvent
  have hFactor : P (A ∩ F ⁻¹' B) =
      P A * P (F ⁻¹' B) :=
    (indepSet_iff_measure_inter_eq_mul hAmbient hEventAmbient P).1 hIndepSet
  exact hFactor
