-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat07b_original_BV_countable_local_C1_discounted_stieltjes_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T10:09:46.746283+00:00
-- url     : https://prove2.me/submissions/f7ddae8c-3572-4fef-943b-f01211eb5572

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_chat07b_original_BV_local_C1_discounted_stieltjes_product
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
noncomputable section

/-- Countable positive-band original stopped BV C1 discounted product rule. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (cap : ℝ)
    (lo hi : ℕ → ℝ)
    (hBand : ∀ n, lo n < hi n)
    (hInside : ∀ n, Icc (lo n) (hi n) ⊆ Ioo 0 cap)
    (hwC1 : ContDiffOn ℝ 1 w (Ioo 0 cap)) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ T : ℝ≥0,
      (∀ t : ℝ≥0,
        x + X.X (min t T) ω - rightLimit D (min t T) ω ∈
          Icc (lo n) (hi n)) →
      let f : ℝ≥0 → ℝ := fun t => Real.exp (-q * (t : ℝ))
      let g : ℝ≥0 → ℝ := fun t =>
        w (x + X.X (min t T) ω - rightLimit D (min t T) ω)
      ∃ hf : BoundedVariationOn f Set.univ,
        ∃ hg : BoundedVariationOn g Set.univ,
          ∀ a b : ℝ≥0, a ≤ b →
            (∫ᵛ t in Ioc a b, Function.leftLim f t ∂• hg.vectorMeasure) =
              Function.rightLim f b • Function.rightLim g b -
              Function.rightLim f a • Function.rightLim g a -
              (∫ᵛ t in Ioc a b, Function.rightLim g t ∂<• hf.vectorMeasure) := by
  apply (MeasureTheory.ae_all_iff).2
  intro n
  exact avram_chat07b_original_BV_local_C1_discounted_stieltjes_product
    X hX hBV x D hD q hq w cap (lo n) (hi n)
    (hBand n) (hInside n) hwC1
