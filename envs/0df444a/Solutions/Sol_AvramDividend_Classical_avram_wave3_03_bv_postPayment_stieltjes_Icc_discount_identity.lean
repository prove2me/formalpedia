-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_bv_postPayment_stieltjes_Icc_discount_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T06:57:19.308753+00:00
-- url     : https://prove2.me/submissions/a131a8ee-8558-44d9-a017-8eff3aa21b04

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discount_exp_global_variation
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_postPayment_truncated_global_variation
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_postPayment_stieltjes_Ioc_discount_identity
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_generic_bv_vector_stieltjes_interval_integrability
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_discount_exp_leftLim_eq_rightLim_on_nnreal
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_generic_bv_stieltjes_Icc_identity_of_Ioc_and_endpoint

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

noncomputable section

/-- Source-complete reduction of the original closed BV post-payment
Stieltjes identity to a half-open identity and explicit BV integrability.
Both imported Open children remain real mathematical obligations. -/
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
            (∫ᵛ t in Icc a b, Function.leftLim f t ∂• hg.vectorMeasure) =
              Function.rightLim f b • Function.rightLim g b -
              Function.leftLim f a • Function.leftLim g a -
              (∫ᵛ t in Icc a b, Function.rightLim g t ∂<• hf.vectorMeasure) := by
  filter_upwards [
    avram_wave3_03_bv_postPayment_stieltjes_Ioc_discount_identity
      X hX hBV x D hD q hq v L hv
  ] with ω hω
  intro T
  dsimp only
  rcases hω T with ⟨hf, hg, hIoc⟩
  refine ⟨hf, hg, ?_⟩
  intro a b hab
  let f : ℝ≥0 → ℝ := fun t => Real.exp (-q * (t : ℝ))
  let g : ℝ≥0 → ℝ := fun t =>
    v (x + X.X (min t T) ω - rightLimit D (min t T) ω)
  obtain ⟨hflIoc, hflAt, hgrIoc, hgrAt⟩ :=
    avram_wave6_05_generic_bv_vector_stieltjes_interval_integrability
      f g hf hg a b hab
  exact avram_wave6_05_generic_bv_stieltjes_Icc_identity_of_Ioc_and_endpoint
    f g hf hg a b hab
    (avram_wave6_05_discount_exp_leftLim_eq_rightLim_on_nnreal q a)
    hflIoc hflAt hgrIoc hgrAt (hIoc a b hab)
