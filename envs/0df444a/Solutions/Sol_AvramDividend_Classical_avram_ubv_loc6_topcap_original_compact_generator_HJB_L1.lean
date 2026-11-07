-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_loc6_topcap_original_compact_generator_HJB_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T00:34:08.890242+00:00
-- url     : https://prove2.me/submissions/3cdba738-642e-4575-bdf8-3e4a53f00d0e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_topcap_positive_halfline_HJB_bridge
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_true_clock_compact_generator_hjb_L1_nonpositive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Compact physical generator HJB source under the original infinite cap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (C : ℝ≥0∞)
    (hD : IsAdmissibleLe X x C D)
    (hTop : C = ⊤)
    (w : ℝ → ℝ)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (u v δ B : ℝ) (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < B)
    (T : ℝ≥0) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let ρ : ℝ≥0 × Ω → ℝ := fun p =>
      if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then 1 else 0
    let R : ℝ≥0 × Ω → ℝ := fun p =>
      ρ p * (if Y p ∈ Icc (u + δ) v then
        X.generator w (Y p) - q * w (Y p) else 0)
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
          μ A = ((((volume : Measure ℝ).restrict
            (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) ∧
      Integrable R μ ∧
      (∫ p, R p ∂μ) ≤ 0 := by
  have hHalf := avram_ubv_loc6_topcap_positive_halfline_HJB_bridge
    X w C hTop hw_smooth q hw_gen hw_grad
  have hSmB : ContDiffOn ℝ 2 w (Ioo 0 B) := by
    apply hHalf.1.mono
    intro y hy
    exact hy.1
  have hGenB : ∀ y : ℝ, 0 < y → y < B →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0 := by
    intro y hy hyB
    exact hHalf.2.1 y hy
  exact avram_wave5_03_original_true_clock_compact_generator_hjb_L1_nonpositive
    X x D hD.1.1 w B u v δ hSmB hw_cont hw_neg
    hu hδ hδone huv hv q T hGenB
