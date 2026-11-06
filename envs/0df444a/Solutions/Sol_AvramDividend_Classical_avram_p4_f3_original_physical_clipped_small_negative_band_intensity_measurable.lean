-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_physical_clipped_small_negative_band_intensity_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T19:23:22.011683+00:00
-- url     : https://prove2.me/submissions/f3c41daf-3b04-4bd2-bff7-8d0cffa2c18b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_predividend_clipped_reserve_jointly_measurable_bounded
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_small_negative_band_arbitrary_source_parameter_L2_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Squared physical small-jump source intensity is measurable on time-by-sample. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (δ K ε : ℝ) (hδK : δ ≤ K) :
    let U : ℝ≥0 × Ω → ℝ := fun p =>
      let y := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
      if y ∈ Icc δ K then y else δ
    Measurable (fun p =>
      (∫⁻ z in Ioo (-ε) (0 : ℝ),
        ENNReal.ofReal
          (((w (U p + z) - w (U p)) -
            (w (δ + z) - w δ)) ^ 2) ∂X.ν)) := by
  obtain ⟨hU, _⟩ :=
    avram_p4_f3_original_predividend_clipped_reserve_jointly_measurable_bounded
      X x D hD δ K hδK
  exact
    avram_p4_f3_original_small_negative_band_arbitrary_source_parameter_L2_measurable
      X w hw_cont hw_neg _ (fun _ => δ) hU measurable_const ε
