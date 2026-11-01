-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_bv_postPayment_stieltjes_Icc_unit_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T09:36:30.812269+00:00
-- url     : https://prove2.me/submissions/b8edf92b-0939-4802-b91f-5a6000331b62

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_postPayment_truncated_global_variation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Exact undiscounted vector-Stieltjes endpoint accounting for the original
    post-payment BV reserve. The closed interval retains its initial atom. -/
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
          (∫ᵛ t in Icc a b, (1 : ℝ) ∂• hg.vectorMeasure) =
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
  refine ⟨hg, ?_⟩
  intro a b hab
  haveI : IsFiniteMeasure (hg.vectorMeasure).variation := by
    rw [← MeasureTheory.SignedMeasure.totalVariation_eq_variation]
    infer_instance
  haveI : IsFiniteMeasure ((hg.vectorMeasure).variation.restrict (Icc a b)) :=
    inferInstance
  rw [MeasureTheory.VectorMeasure.setIntegral_const]
  simpa using hg.vectorMeasure_Icc hab
