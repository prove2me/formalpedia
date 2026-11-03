-- Prove2me | solution 2 for AvramDividend.Classical.avram_wave3_03_bv_postPayment_stieltjes_Ioc_discount_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T07:47:47.101244+00:00
-- url     : https://prove2.me/submissions/22ea3eca-384e-48d7-9974-50a363e70c18

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discount_exp_global_variation
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_postPayment_truncated_global_variation
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_generic_bv_stieltjes_Ioc_product_of_fubini
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_generic_bv_stieltjes_Ioc_fubini_exchange

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Exact source-path BV integration by parts reduced to the genuine
    generic ordered-triangle vector Stieltjes Fubini exchange. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
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
  filter_upwards [
    avram_wave3_03_bv_postPayment_truncated_global_variation X hX hBV x D hD
  ] with ω hω
  intro T
  dsimp only
  have hf : BoundedVariationOn
      (fun t : ℝ≥0 => Real.exp (-q * (t : ℝ))) Set.univ :=
    avram_wave3_03_bv_discount_exp_global_variation q hq
  have hg : BoundedVariationOn
      (fun t : ℝ≥0 =>
        v (x + X.X (min t T) ω - rightLimit D (min t T) ω))
      Set.univ := by
    simpa only [Function.comp_def] using
      hv.comp_boundedVariationOn (hω T)
  refine ⟨hf, hg, ?_⟩
  intro a b hab
  let B : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
  have hB : B.flip = B := by
    ext y z <;> simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply] <;> exact mul_comm z y
  have hFubini : (∫ᵛ t in Ioc a b,
      (Function.rightLim
        (fun t : ℝ≥0 => v (x + X.X (min t T) ω - rightLimit D (min t T) ω)) t -
       Function.rightLim
        (fun t : ℝ≥0 => v (x + X.X (min t T) ω - rightLimit D (min t T) ω)) a)
        ∂<• hf.vectorMeasure) =
      (∫ᵛ t in Ioc a b,
        (Function.rightLim (fun t : ℝ≥0 => Real.exp (-q * (t : ℝ))) b -
         Function.leftLim (fun t : ℝ≥0 => Real.exp (-q * (t : ℝ))) t)
        ∂• hg.vectorMeasure) := by
    change (∫ᵛ t in Ioc a b,
        (Function.rightLim
          (fun t : ℝ≥0 => v (x + X.X (min t T) ω - rightLimit D (min t T) ω)) t -
         Function.rightLim
          (fun t : ℝ≥0 => v (x + X.X (min t T) ω - rightLimit D (min t T) ω)) a)
        ∂[B.flip; hf.vectorMeasure]) =
      (∫ᵛ t in Ioc a b,
        (Function.rightLim (fun t : ℝ≥0 => Real.exp (-q * (t : ℝ))) b -
         Function.leftLim (fun t : ℝ≥0 => Real.exp (-q * (t : ℝ))) t)
        ∂[B; hg.vectorMeasure])
    rw [hB]
    exact avram_wave6_05_generic_bv_stieltjes_Ioc_fubini_exchange _ _ hf hg a b hab
  exact avram_wave6_05_generic_bv_stieltjes_Ioc_product_of_fubini
    _ _ hf hg a b hab hFubini
