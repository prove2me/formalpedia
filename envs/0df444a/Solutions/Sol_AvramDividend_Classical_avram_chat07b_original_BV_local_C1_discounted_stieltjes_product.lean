-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat07b_original_BV_local_C1_discounted_stieltjes_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T08:06:01.712878+00:00
-- url     : https://prove2.me/submissions/d79cd911-fcce-45a9-8059-24f356c4c599

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_chat07b_original_BV_local_C1_postpayment_composition
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discount_exp_global_variation
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_generic_bv_stieltjes_Ioc_product_of_fubini
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_generic_bv_stieltjes_Ioc_fubini_exchange
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (cap lo hi : ℝ)
    (hlr : lo < hi) (hsub : Icc lo hi ⊆ Ioo 0 cap)
    (hwC1 : ContDiffOn ℝ 1 w (Ioo 0 cap)) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      (∀ t : ℝ≥0,
        x + X.X (min t T) ω - rightLimit D (min t T) ω ∈ Icc lo hi) →
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
  filter_upwards [
    avram_chat07b_original_BV_local_C1_postpayment_composition
      X hX hBV x D hD w cap lo hi hlr hsub hwC1
  ] with ω hω
  intro T hstay
  dsimp only
  have hf : BoundedVariationOn
      (fun t : ℝ≥0 => Real.exp (-q * (t : ℝ))) Set.univ :=
    avram_wave3_03_bv_discount_exp_global_variation q hq
  have hg : BoundedVariationOn
      (fun t : ℝ≥0 =>
        w (x + X.X (min t T) ω - rightLimit D (min t T) ω))
      Set.univ := hω T hstay
  refine ⟨hf, hg, ?_⟩
  intro a b hab
  let B : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
  have hB : B.flip = B := by
    ext y z <;> simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply] <;> exact mul_comm z y
  have hFubini : (∫ᵛ t in Ioc a b,
      (Function.rightLim
        (fun t : ℝ≥0 => w (x + X.X (min t T) ω - rightLimit D (min t T) ω)) t -
       Function.rightLim
        (fun t : ℝ≥0 => w (x + X.X (min t T) ω - rightLimit D (min t T) ω)) a)
        ∂<• hf.vectorMeasure) =
      (∫ᵛ t in Ioc a b,
        (Function.rightLim (fun t : ℝ≥0 => Real.exp (-q * (t : ℝ))) b -
         Function.leftLim (fun t : ℝ≥0 => Real.exp (-q * (t : ℝ))) t)
        ∂• hg.vectorMeasure) := by
    change (∫ᵛ t in Ioc a b,
        (Function.rightLim
          (fun t : ℝ≥0 => w (x + X.X (min t T) ω - rightLimit D (min t T) ω)) t -
         Function.rightLim
          (fun t : ℝ≥0 => w (x + X.X (min t T) ω - rightLimit D (min t T) ω)) a)
        ∂[B.flip; hf.vectorMeasure]) =
      (∫ᵛ t in Ioc a b,
        (Function.rightLim (fun t : ℝ≥0 => Real.exp (-q * (t : ℝ))) b -
         Function.leftLim (fun t : ℝ≥0 => Real.exp (-q * (t : ℝ))) t)
        ∂[B; hg.vectorMeasure])
    rw [hB]
    exact avram_wave6_05_generic_bv_stieltjes_Ioc_fubini_exchange _ _ hf hg a b hab
  exact avram_wave6_05_generic_bv_stieltjes_Ioc_product_of_fubini
    _ _ hf hg a b hab hFubini
