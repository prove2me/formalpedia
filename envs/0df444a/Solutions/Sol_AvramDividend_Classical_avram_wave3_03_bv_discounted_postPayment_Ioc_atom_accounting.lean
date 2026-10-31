-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_bv_discounted_postPayment_Ioc_atom_accounting
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T21:15:58.503006+00:00
-- url     : https://prove2.me/submissions/31d15d55-5cf5-4b14-bcd2-778cd3f2001c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_postPayment_truncated_global_variation
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discount_exp_global_variation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The source-controlled BV reserve gives a discounted Stieltjes
    measure whose open-closed mass and individual atoms agree exactly
    with the corresponding one-sided path increments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q)
    (v : ℝ → ℝ) (L : NNReal) (hv : LipschitzWith L v) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      let g : ℝ≥0 → ℝ := fun t =>
        Real.exp (-q * (t : ℝ)) *
          v (x + X.X (min t T) ω - rightLimit D (min t T) ω)
      ∃ hg : BoundedVariationOn g Set.univ,
        ∀ a b : ℝ≥0, a ≤ b →
          hg.vectorMeasure (Ioc a b) =
            Function.rightLim g b - Function.rightLim g a ∧
          hg.vectorMeasure ({a} : Set ℝ≥0) =
            Function.rightLim g a - Function.leftLim g a := by
  filter_upwards [
    avram_wave3_03_bv_postPayment_truncated_global_variation X hX hBV x D hD
  ] with ω hω
  intro T
  dsimp only
  have hvpath : BoundedVariationOn
      (fun t : ℝ≥0 => v (x + X.X (min t T) ω - rightLimit D (min t T) ω))
      Set.univ := by
    simpa only [Function.comp_def] using hv.comp_boundedVariationOn (hω T)
  have hg : BoundedVariationOn
      (fun t : ℝ≥0 => Real.exp (-q * (t : ℝ)) *
        v (x + X.X (min t T) ω - rightLimit D (min t T) ω))
      Set.univ :=
    (avram_wave3_03_bv_discount_exp_global_variation q hq).fun_mul hvpath
  exact ⟨hg, fun a b hab => ⟨hg.vectorMeasure_Ioc hab, hg.vectorMeasure_singleton⟩⟩
