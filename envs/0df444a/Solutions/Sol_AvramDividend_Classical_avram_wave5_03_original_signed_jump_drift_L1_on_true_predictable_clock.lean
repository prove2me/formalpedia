-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03_original_signed_jump_drift_L1_on_true_predictable_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T14:20:16.195293+00:00
-- url     : https://prove2.me/submissions/9b5f5c53-ae17-426b-be11-8bac75305217

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_generator_signed_drift_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_finite_horizon_full_negative_C2_generator_signed_drift_L1_energy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The source signed nonlinear jump drift, in the actual predictable prepayment
reserve, has a true finite-horizon L¹ integral on the original filtration clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : ∀ f : (ℝ≥0 × Ω) → ℝ≥0∞,
      Measurable[𝓕.rightCont.predictable] f →
      (∫⁻ p, f p ∂μ) =
        (∫⁻ p, f p ∂((((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal).prod P))) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    Integrable (fun p : ℝ≥0 × Ω =>
      ∫ z in Iio (0 : ℝ), JG (p,z) ∂X.ν) μ := by
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
    (if Y p.1 ∈ Icc (u + δ) v then
      SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
  change Integrable (fun p : ℝ≥0 × Ω =>
    ∫ z in Iio (0 : ℝ), JG (p,z) ∂X.ν) μ
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  have hm : Measurable[𝓕.rightCont.predictable]
      (fun p : ℝ≥0 × Ω =>
        ∫ z in Iio (0 : ℝ), JG (p,z) ∂X.ν) := by
    simpa only [Y, JG] using
      avram_wave5_03b_actual_ruin_stopped_full_negative_C2_generator_signed_drift_predictable
        X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv
  have he : (∫⁻ p : ℝ≥0 × Ω,
      ‖∫ z in Iio (0 : ℝ), JG (p,z) ∂X.ν‖ₑ ∂μ) < ⊤ := by
    rw [hμ _ hm.enorm]
    exact avram_wave5_03b_actual_finite_horizon_full_negative_C2_generator_signed_drift_L1_energy
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv T
  exact ⟨hm.aestronglyMeasurable, he⟩
