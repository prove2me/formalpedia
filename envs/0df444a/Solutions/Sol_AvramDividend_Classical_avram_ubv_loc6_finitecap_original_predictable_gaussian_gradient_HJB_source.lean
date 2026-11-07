-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_loc6_finitecap_original_predictable_gaussian_gradient_HJB_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T00:34:11.667519+00:00
-- url     : https://prove2.me/submissions/fb5f3d42-14b9-4bb1-b4a6-c2fa4d25632f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_finitecap_original_compact_generator_HJB_L1
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_allcap_original_predictable_gradient_compact_L2_from_C2_domain

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A common original predictable source measure carries both the stopped
    HJB drift and a finite-energy predictable Gaussian derivative coefficient. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (C : ℝ≥0∞)
    (hD : IsAdmissibleLe X x C D)
    (hC : 0 < C) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (u v δ a b : ℝ) (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C.toReal)
    (ha : 0 < a) (hau : a < u + δ) (hvb : v < b)
    (hb : b < C.toReal)
    (T : ℝ≥0) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let ρ : ℝ≥0 × Ω → ℝ := fun p =>
      if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then 1 else 0
    let R : ℝ≥0 × Ω → ℝ := fun p =>
      ρ p * (if Y p ∈ Icc (u + δ) v then
        X.generator w (Y p) - q * w (Y p) else 0)
    let H : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc (u + δ) v then deriv w (Y p) else 0
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
          μ A = ((((volume : Measure ℝ).restrict
            (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) ∧
      Integrable R μ ∧
      (∫ p, R p ∂μ) ≤ 0 ∧
      Measurable[𝓕.rightCont.predictable] H ∧
      (∫⁻ p : ℝ≥0 × Ω, ENNReal.ofReal ((H p) ^ 2) ∂μ) < ⊤ := by
  have hBand : ∀ y : ℝ, y ∈ Ioo a b → ENNReal.ofReal y < C := by
    intro y hy
    have hypos : 0 ≤ y := le_of_lt (lt_trans ha hy.1)
    exact (ENNReal.ofReal_lt_iff_lt_toReal hypos hFinite).2
      (lt_trans hy.2 hb)
  obtain ⟨μ, hμ, hμeq, hRI, hRnonpos⟩ :=
    avram_ubv_loc6_finitecap_original_compact_generator_HJB_L1
      X x D C hD hC hFinite w hw_smooth hw_cont hw_neg q
      hw_gen hw_grad u v δ hu hδ hδone huv hv T
  have hGaussian :=
    avram_wave7_18_allcap_original_predictable_gradient_compact_L2_from_C2_domain
      X x C D hD w hw_smooth a b (u + δ) v
      ha hau (le_of_lt huv) hvb hBand μ hμ
  exact ⟨μ, hμ, hμeq, hRI, hRnonpos, hGaussian.1, hGaussian.2⟩
