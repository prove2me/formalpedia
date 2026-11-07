-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_turn52_origin_value_positive_of_BV_HJB
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T10:22:21.474107+00:00
-- url     : https://prove2.me/submissions/ba585e4e-08dd-46ec-9a03-0a8b2548422c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_positive_initial_value_of_positive_reserve
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn53_origin_integrated_BV_HJB_budget
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn54_original_BV_truncated_moment_small
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact integrated HJB inequality at zero contradicts the small-jump
    first-moment gap for sufficiently small, strictly positive reserves. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hDrift : 0 < X.drift) :
    0 < w 0 := by
  by_contra hnot
  have hwzero : w 0 = 0 := le_antisymm (le_of_not_gt hnot) hw0
  obtain ⟨ε, hε, hεC, hε1, hSmall⟩ :=
    avram_bv_env3_turn54_original_BV_truncated_moment_small
      X hBV q hq C hC hDrift
  have hwεpos : 0 < w ε :=
    avram_p3_grid4_positive_initial_value_of_positive_reserve
      C hC w hw_cont hw0 hw_smooth hw_grad ε hε (le_of_lt hεC)
  have hBudget := avram_bv_env3_turn53_origin_integrated_BV_HJB_budget
    X hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
    hw_gen hw_grad hwzero ε hε hεC hε1
  have hStrict :
      (q * ε + ∫ z in Iio (0 : ℝ), min ε (-z) ∂X.ν) * w ε <
        X.drift * w ε := mul_lt_mul_of_pos_right hSmall hwεpos
  exact (not_lt_of_ge hBudget) hStrict
