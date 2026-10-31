-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_bv_postPayment_vectorMeasure_Icc_atom_accounting
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T21:11:04.196953+00:00
-- url     : https://prove2.me/submissions/80a91a2a-09ae-4c16-8fd4-124c90a5acfc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_postPayment_truncated_global_variation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The Stieltjes vector measure of the genuine post-payment BV test
    accounts for both right-side and left-side dividend atoms exactly. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (v : ℝ → ℝ) (L : NNReal) (hv : LipschitzWith L v) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      let g : ℝ≥0 → ℝ := fun t =>
        v (x + X.X (min t T) ω - rightLimit D (min t T) ω)
      ∃ hg : BoundedVariationOn g Set.univ,
        ∀ a b : ℝ≥0, a ≤ b →
          hg.vectorMeasure (Icc a b) =
            Function.rightLim g b - Function.leftLim g a := by
  filter_upwards [
    avram_wave3_03_bv_postPayment_truncated_global_variation X hX hBV x D hD
  ] with ω hω
  intro T
  dsimp only
  have hg : BoundedVariationOn
      (fun t : ℝ≥0 => v (x + X.X (min t T) ω - rightLimit D (min t T) ω))
      Set.univ := by
    simpa only [Function.comp_def] using hv.comp_boundedVariationOn (hω T)
  exact ⟨hg, fun a b hab => hg.vectorMeasure_Icc hab⟩
