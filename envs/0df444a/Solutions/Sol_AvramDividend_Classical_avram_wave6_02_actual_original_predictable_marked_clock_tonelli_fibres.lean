-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_02_actual_original_predictable_marked_clock_tonelli_fibres
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T09:22:04.566787+00:00
-- url     : https://prove2.me/submissions/9b621d27-d441-4611-a865-081504c9171c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_source_finite_horizon_predictable_lintegral_eq_time_probability
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) :
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
        μ A = ((((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) ∧
      (∀ G : ((ℝ≥0 × Ω) × ℝ) → ℝ≥0∞,
        Measurable[(@Prod.instMeasurableSpace _ _
          (𝓕.rightCont.predictable)
          (inferInstance : MeasurableSpace ℝ))] G →
        Measurable G →
        (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
          ∫⁻ p, G p ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ))))) =
        ∫⁻ ω, ∫⁻ t, ∫⁻ z, G ((t, ω), z)
          ∂(X.ν.restrict (Iio (0 : ℝ)))
          ∂(((volume : Measure ℝ).restrict
            (Icc 0 (T : ℝ))).map Real.toNNReal) ∂P) := by
  classical
  rcases avram_wave4_04b_source_finite_horizon_predictable_lintegral_eq_time_probability
    X T with ⟨μ, hμfinite, hμclock, hμint⟩
  refine ⟨μ, hμfinite, hμclock, ?_⟩
  intro G hG hGambient
  let ν : Measure ℝ := X.ν.restrict (Iio (0 : ℝ))
  letI : SFinite ν := levy_negative_jump_measure_sFinite X
  letI : IsProbabilityMeasure P := X.isProbability
  let ηReal : Measure ℝ := (volume : Measure ℝ).restrict (Icc 0 (T : ℝ))
  have hηReal : ηReal Set.univ < ⊤ := by
    simpa [ηReal] using (isCompact_Icc.measure_lt_top (μ := (volume : Measure ℝ)))
  letI : IsFiniteMeasure ηReal := ⟨hηReal⟩
  let η : Measure ℝ≥0 := ηReal.map Real.toNNReal
  letI : IsFiniteMeasure η := Measure.isFiniteMeasure_map ηReal Real.toNNReal
  have hInnerPred :
      Measurable[𝓕.rightCont.predictable]
        (fun p : ℝ≥0 × Ω => ∫⁻ z, G (p, z) ∂ν) := by
    letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
    exact Measurable.lintegral_prod_right hG
  have hInnerAmbient :
      Measurable
        (fun p : ℝ≥0 × Ω => ∫⁻ z, G (p, z) ∂ν) :=
    Measurable.lintegral_prod_right hGambient
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  calc
    (∫⁻ p, G p ∂(μ.prod ν)) =
        ∫⁻ p, ∫⁻ z, G (p, z) ∂ν ∂μ :=
      lintegral_prod G hG.aemeasurable
    _ = ∫⁻ p, ∫⁻ z, G (p, z) ∂ν ∂(η.prod P) := by
      exact hμint _ hInnerPred
    _ = ∫⁻ ω, ∫⁻ t, ∫⁻ z, G ((t, ω), z) ∂ν ∂η ∂P := by
      exact lintegral_prod_symm _ hInnerAmbient.aemeasurable
