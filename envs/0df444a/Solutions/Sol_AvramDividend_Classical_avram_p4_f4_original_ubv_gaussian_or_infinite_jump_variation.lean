-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f4_original_ubv_gaussian_or_infinite_jump_variation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:46:22.552357+00:00
-- url     : https://prove2.me/submissions/4ce917c7-d3ec-4b62-8118-f4ef66ce2034

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_original_purejump_ubv_infinite_variation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation) :
    X.σ ≠ 0 ∨ (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν) = ⊤ := by
  by_cases hσ : X.σ = 0
  · right
    exact avram_p4_f4_original_purejump_ubv_infinite_variation X hBV hσ
  · exact Or.inl hσ
