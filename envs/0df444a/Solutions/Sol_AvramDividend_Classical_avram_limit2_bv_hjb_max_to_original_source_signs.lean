-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_bv_hjb_max_to_original_source_signs
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T19:58:28.371241+00:00
-- url     : https://prove2.me/submissions/7cb14b8b-46e6-4e3d-ad3b-4dea4163cbb5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_bv_hjb_max_zero_implies_slope_one
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The original BV HJB maximum gives both hypotheses needed by the
    signed physical-grid source certificate and its perpetual-value adapter. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0) :
    (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) ∧
    (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y) := by
  constructor
  · intro y hy hyC
    rcases hw_hjb y hy hyC with ⟨hIntegrable, hMax⟩
    refine ⟨hIntegrable, ?_⟩
    exact le_trans (le_max_left _ _) (le_of_eq hMax)
  · exact avram_limit2_bv_hjb_max_zero_implies_slope_one
      X q w C hw_hjb
