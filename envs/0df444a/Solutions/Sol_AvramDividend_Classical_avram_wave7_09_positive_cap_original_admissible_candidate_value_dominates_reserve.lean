-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_09_positive_cap_original_admissible_candidate_value_dominates_reserve
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:57:02.253584+00:00
-- url     : https://prove2.me/submissions/2891c8b5-faf9-45a3-8d9f-4bba2c36e903

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_allCap_admissible_initial_capital_nonneg
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The corrected positive-cap boundary hypotheses force the original
admissible initial reserve to be nonnegative and the HJB candidate
value to dominate that reserve, including both cap endpoints. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    0 ≤ x ∧ x ≤ w x := by
  have hx : 0 ≤ x :=
    avram_wave3_04_allCap_admissible_initial_capital_nonneg
      X x C hxc D hD
  have hsec :=
    avram_wave3_03_bv_full_cap_gradient_secant
      C hC w hw_cont hw_smooth hw_grad 0 x
      (le_refl (0 : ℝ)) hx hxc
  constructor
  · exact hx
  · linarith
