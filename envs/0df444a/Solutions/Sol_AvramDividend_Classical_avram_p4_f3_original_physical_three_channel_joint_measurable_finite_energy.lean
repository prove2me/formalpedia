-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_physical_three_channel_joint_measurable_finite_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T19:37:11.398779+00:00
-- url     : https://prove2.me/submissions/5c6b927e-5688-47ba-95e3-2d3883f97f72

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_predividend_clipped_reserve_jointly_measurable_bounded
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_physical_clipped_small_negative_band_intensity_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_large_negative_band_arbitrary_source_intensity_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_physical_clipped_gaussian_small_large_joint_L2_energy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- All same-source Gaussian and small/large jump coefficients have measurable finite intensity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ K ε : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C) (hε : 0 < ε)
    (μ : Measure (ℝ≥0 × Ω)) (hμ : μ univ < ⊤) :
    let U : ℝ≥0 × Ω → ℝ := fun p =>
      let y := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
      if y ∈ Icc δ K then y else δ
    Measurable U ∧
    Measurable (fun p =>
      (∫⁻ z in Ioo (-ε) (0 : ℝ),
        ENNReal.ofReal
          (((w (U p + z) - w (U p)) -
            (w (δ + z) - w δ)) ^ 2) ∂X.ν)) ∧
    Measurable (fun p =>
      (∫⁻ z in Iic (-ε),
        ENNReal.ofReal ((w (U p + z) - w (U p)) ^ 2) ∂X.ν)) ∧
    ((∫⁻ p, ENNReal.ofReal ((X.σ * deriv w (U p)) ^ 2) ∂μ) < ⊤ ∧
     (∫⁻ p, (∫⁻ z in Ioo (-ε) (0 : ℝ),
       ENNReal.ofReal
         (((w (U p + z) - w (U p)) -
           (w (δ + z) - w δ)) ^ 2) ∂X.ν) ∂μ) < ⊤) ∧
    (∫⁻ p, (∫⁻ z in Iic (-ε),
      ENNReal.ofReal ((w (U p + z) - w (U p)) ^ 2) ∂X.ν) ∂μ) < ⊤ := by
  have hU : Measurable (fun p : ℝ≥0 × Ω =>
      let y := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
      if y ∈ Icc δ K then y else δ) :=
    (avram_p4_f3_original_predividend_clipped_reserve_jointly_measurable_bounded
      X x D hD δ K hδK).1
  have hs :=
    avram_p4_f3_original_physical_clipped_small_negative_band_intensity_measurable
      X x D hD w hw_cont hw_neg δ K ε hδK
  have hl :=
    avram_p4_f3_original_large_negative_band_arbitrary_source_intensity_measurable
      X w hw_cont hw_neg _ hU ε
  have he :=
    avram_p4_f3_original_physical_clipped_gaussian_small_large_joint_L2_energy
      X x D w C hw_cont hw_neg hw_smooth δ K ε hδ hδK hK hε μ hμ
  exact ⟨hU, hs, hl, he⟩
