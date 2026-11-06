-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_positive_small_jump_random_reserve_joint_L2_dct
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:27:32.010497+00:00
-- url     : https://prove2.me/submissions/670a310a-b30d-45d9-a679-e7c695d826d7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_small_negative_band_random_reserve_coefficient_L2_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_positive_small_jump_random_reserve_joint_L2_dct_of_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original positive-reserve random mesh coefficients converge in physical joint L2 without an extra measurability premise. -/
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
    (U : ℕ → Ω → ℝ) (u : Ω → ℝ)
    (hUmeas : ∀ k, Measurable (U k)) (humeas : Measurable u)
    (hUb : ∀ k ω, U k ω ∈ Icc δ K)
    (hub : ∀ ω, u ω ∈ Icc δ K)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun k => U k ω) atTop (𝓝 (u ω))) :
    Tendsto (fun k =>
      (∫⁻ ω, (∫⁻ z in Ioo (-ε) (0 : ℝ),
        ENNReal.ofReal
          (((w (U k ω + z) - w (U k ω)) -
            (w (u ω + z) - w (u ω))) ^ 2) ∂X.ν) ∂P))
      atTop (𝓝 (0 : ℝ≥0∞)) := by
  letI : IsProbabilityMeasure P := X.isProbability
  exact
    avram_p4_f3_original_positive_small_jump_random_reserve_joint_L2_dct_of_measurable
      X w C hw_cont hw_neg hw_smooth δ K ε
      hδ hδK hK hε hεδ U u hUb hub
      (fun k =>
        avram_p4_f3_original_small_negative_band_random_reserve_coefficient_L2_measurable
          X w hw_cont hw_neg (U k) u (hUmeas k) humeas ε)
      hlim
