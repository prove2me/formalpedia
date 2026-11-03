-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_negative_predictable_mark_fibre_compensator_expected_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:04:34.4216+00:00
-- url     : https://prove2.me/submissions/6901fd07-bfcd-42ba-b65a-86ab5e71c2cb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_original_rightcont_predictable_signed_mark_compensator_fibre_Fubini
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Original right-continuous predictable negative-mark kernel has a genuine
integrable random time-compensator with nonpositive expectation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (G : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hGMeas : Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable)
      (inferInstance : MeasurableSpace ℝ))] G)
    (hGNeg : ∀ p, G p ≤ 0)
    (hGInt : ∀ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ →
      (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
        Integrable G (μ.prod (X.ν.restrict (Iio (0 : ℝ)))))) :
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
        μ A = ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
          Real.toNNReal).prod P) A) ∧
      Integrable (fun ω => ∫ t, ∫ z, G ((t, ω), z)
        ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal)) P ∧
      (∫ ω, (∫ t, ∫ z, G ((t, ω), z)
        ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal)) ∂P) ≤ 0 := by
  obtain ⟨μ, hFinite, hClock, hFubini⟩ :=
    avram_wave6_02_original_rightcont_predictable_signed_mark_compensator_fibre_Fubini X T
  obtain ⟨hPathInt, hMean⟩ := hFubini G hGMeas (hGInt μ hFinite)
  have hProdNonpos : (letI : MeasurableSpace (ℝ≥0 × Ω) :=
      𝓕.rightCont.predictable;
      ∫ p, G p ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ))))) ≤ 0 := by
    letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
    apply MeasureTheory.integral_nonpos_of_ae
    exact Filter.Eventually.of_forall hGNeg
  refine ⟨μ, hFinite, hClock, hPathInt, ?_⟩
  rw [hMean]
  exact hProdNonpos
