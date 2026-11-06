-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_negative_band_finite_source_parameter_L2_dct
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:41:26.699762+00:00
-- url     : https://prove2.me/submissions/b6146d8d-e0ad-4511-ad13-2b6a7b04e99a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_negative_band_finite_source_parameter_L2_dct_of_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_small_negative_band_arbitrary_source_parameter_L2_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Physical joint small-jump L² convergence over finite time-space source measures, with measurability discharged. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ K ε : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C)
    (hε : 0 < ε) (hεδ : ε < δ)
    {S : Type*} [mS : MeasurableSpace S]
    (μ : Measure S) (hμ : μ univ < ⊤)
    (U : ℕ → S → ℝ) (u : S → ℝ)
    (hUmeas : ∀ k, Measurable (U k)) (humeas : Measurable u)
    (hUb : ∀ k s, U k s ∈ Icc δ K)
    (hub : ∀ s, u s ∈ Icc δ K)
    (hlim : ∀ᵐ s ∂μ, Tendsto (fun k => U k s) atTop (𝓝 (u s))) :
    Tendsto (fun k =>
      (∫⁻ s, (∫⁻ z in Ioo (-ε) (0 : ℝ),
        ENNReal.ofReal
          (((w (U k s + z) - w (U k s)) -
            (w (u s + z) - w (u s))) ^ 2) ∂X.ν) ∂μ))
      atTop (𝓝 (0 : ℝ≥0∞)) := by
  exact
    avram_p4_f3_original_negative_band_finite_source_parameter_L2_dct_of_measurable
      X w C hw_cont hw_neg hw_smooth δ K ε
      hδ hδK hK hε hεδ μ hμ U u hUb hub
      (fun k =>
        avram_p4_f3_original_small_negative_band_arbitrary_source_parameter_L2_measurable
          X w hw_cont hw_neg (U k) u (hUmeas k) humeas ε)
      hlim
