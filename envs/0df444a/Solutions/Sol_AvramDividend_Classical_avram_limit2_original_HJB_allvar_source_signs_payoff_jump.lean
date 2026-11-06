-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_original_HJB_allvar_source_signs_payoff_jump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T21:58:07.8882+00:00
-- url     : https://prove2.me/submissions/91dee4be-c4be-4d6f-9a3f-24a150f69f4c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_bv_hjb_max_to_original_source_signs
import Theorems.Thm_AvramDividend_Classical_avram_limit2_bv_original_C1_path_and_right_jump_premises
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_HJB_all_variation_payoff_above_reserve
import Theorems.Thm_AvramDividend_Classical_capped_riskProcess_range_before_ruin_including_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Common original BV/UBV HJB, physical reserve, and right-payment source
    interface with quantitative pre-ruin reserve domination. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0)
    (hwCont : ContinuousOn w (Ici (0 : ℝ)))
    (hwBV : X.BoundedVariation →
      ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwUBV : ¬ X.BoundedVariation →
      ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwHJB : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0) :
    (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) ∧
    (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) ∧
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ (D : ℝ≥0 → Ω → ℝ), IsAdmissibleLe X x C D →
      (∀ ω (t : ℝ≥0), 0 < t →
        (t : ℝ≥0∞) < ruinTime X x D ω →
        0 ≤ w (riskProcess X x D t ω)) ∧
      (∀ ω (t : ℝ≥0),
        (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
        rightLimit D t ω - D t ω ≤
          w (riskProcess X x D t ω) -
            w (riskProcess X x D t ω -
              (rightLimit D t ω - D t ω)))) ∧
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ (D : ℝ≥0 → Ω → ℝ), IsAdmissibleLe X x C D →
      ∀ ω (t : ℝ≥0),
        (t : ℝ≥0∞) < ruinTime X x D ω →
        riskProcess X x D t ω ≤ w (riskProcess X x D t ω)) := by
  obtain ⟨hGen, hGrad⟩ :=
    avram_limit2_bv_hjb_max_to_original_source_signs X q w C hwHJB
  have hC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
    by_cases hBV : X.BoundedVariation
    · exact hwBV hBV
    · exact (hwUBV hBV).of_le (by norm_num)
  have hPhysical :=
    avram_limit2_bv_original_C1_path_and_right_jump_premises
      X C hC w hwCont hw0 hC1 hGrad
  have hFloor :=
    avram_limit2_original_HJB_all_variation_payoff_above_reserve
      X q w C hC hw0 hwCont hwBV hwUBV hwHJB
  refine ⟨hGen, hGrad, hPhysical, ?_⟩
  intro x hx hxc D hD ω t ht
  obtain ⟨hy0, hyC⟩ :=
    capped_riskProcess_range_before_ruin_including_zero
      X x hx C hxc D hD ω t ht
  exact hFloor _ hy0 hyC
