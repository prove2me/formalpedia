-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_actual_clock_jump_drift_L1_indicator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:56:21.83038+00:00
-- url     : https://prove2.me/submissions/32a2cf0b-69f9-4fb9-acf9-365da7835b53

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_signed_jump_drift_L1_on_true_predictable_clock
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_actual_stopped_jump_drift_indicator
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Original stopped Lévy generator jump drift is L¹ as an indicator
of the actual source integral on the true predictable physical clock. -/
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
    let A : Set (ℝ≥0 × Ω) :=
      {p | (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 ∧ Y p ∈ Icc (u + δ) v}
    Integrable (A.indicator (fun p =>
      ∫ z in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand w (Y p) z ∂X.ν)) μ := by
  intro Y A
  have hJG :=
    avram_wave5_03_original_signed_jump_drift_L1_on_true_predictable_clock
      X x D hD w C u v δ hw hw_cont hw_neg
      hu hδ hδone huv hv T μ hμ
  have hId :=
    avram_p4_c_generator_actual_stopped_jump_drift_indicator
      X x D w (u + δ) v
  dsimp at hJG hId
  convert hJG using 1
  funext p
  exact (hId p).symm
