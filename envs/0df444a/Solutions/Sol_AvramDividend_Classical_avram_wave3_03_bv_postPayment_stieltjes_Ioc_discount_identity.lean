-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_bv_postPayment_stieltjes_Ioc_discount_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T07:47:23.10831+00:00
-- url     : https://prove2.me/submissions/a3c84903-fc25-4fda-817d-af7963198751

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discount_exp_global_variation
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_postPayment_truncated_global_variation
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_generic_bv_stieltjes_Ioc_fubini_exchange
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_generic_bv_stieltjes_Ioc_product_of_fubini
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q)
    (v : ℝ → ℝ) (L : NNReal) (hv : LipschitzWith L v) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      let f : ℝ≥0 → ℝ := fun t => Real.exp (-q * (t : ℝ))
      let g : ℝ≥0 → ℝ := fun t =>
        v (x + X.X (min t T) ω - rightLimit D (min t T) ω)
      ∃ hf : BoundedVariationOn f Set.univ,
        ∃ hg : BoundedVariationOn g Set.univ,
          ∀ a b : ℝ≥0, a ≤ b →
            (∫ᵛ t in Ioc a b, Function.leftLim f t ∂• hg.vectorMeasure) =
              Function.rightLim f b • Function.rightLim g b -
              Function.rightLim f a • Function.rightLim g a -
              (∫ᵛ t in Ioc a b, Function.rightLim g t ∂<• hf.vectorMeasure) := by
  filter_upwards
    [avram_wave3_03_bv_postPayment_truncated_global_variation X hX hBV x D hD]
    with ω hω
  intro T
  let f : ℝ≥0 → ℝ := fun t => Real.exp (-q * (t : ℝ))
  let g : ℝ≥0 → ℝ := fun t =>
    v (x + X.X (min t T) ω - rightLimit D (min t T) ω)
  have hf : BoundedVariationOn f Set.univ :=
    avram_wave3_03_bv_discount_exp_global_variation q hq
  have hg : BoundedVariationOn g Set.univ :=
    hv.comp_boundedVariationOn (hω T)
  refine ⟨hf, hg, ?_⟩
  intro a b hab
  have hFubini :
      (∫ᵛ t in Ioc a b,
        (Function.rightLim g t - Function.rightLim g a) ∂<• hf.vectorMeasure) =
      (∫ᵛ t in Ioc a b,
        (Function.rightLim f b - Function.leftLim f t) ∂• hg.vectorMeasure) := by
    have hB : (ContinuousLinearMap.lsmul ℝ ℝ).flip =
        ContinuousLinearMap.lsmul ℝ ℝ := by
      ext u w <;> simp [ContinuousLinearMap.flip_apply, smul_eq_mul, mul_comm]
    rw [hB]
    exact avram_wave6_05_generic_bv_stieltjes_Ioc_fubini_exchange
      f g hf hg a b hab
  exact avram_wave6_05_generic_bv_stieltjes_Ioc_product_of_fubini
    f g hf hg a b hab hFubini
