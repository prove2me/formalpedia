-- Prove2me | solution 2 for AvramDividend.Classical.barrier_value_scale_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T10:17:37.782181+00:00
-- url     : https://prove2.me/submissions/e5afcc0d-6047-408c-8cda-50e50b1f3114

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_value_eq_killed_exit_mul_supValue
import Theorems.Thm_AvramDividend_Classical_two_sided_exit_before_ruin_integral_identity
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    0 < W a ∧
      dividendValue X q x (barrierStrategy X x a)
        = ENNReal.ofReal (W x / W a) * dividendValue X q a (barrierStrategy X a a) := by
  have hWa : 0 < W a := scaleFunction_strict_pos_of_standing X hX q hq W hW a ha
  have hWnn : ∀ y : ℝ, 0 ≤ y → 0 ≤ W y := hW.2.1
  have hWane : W a ≠ 0 := ne_of_gt hWa
  have hfx := barrierStrategy_value_eq_killed_exit_mul_supValue X hX q hq a x ha hx0 hxa
  have hfa := barrierStrategy_value_eq_killed_exit_mul_supValue X hX q hq a a ha ha.le (le_refl a)
  have hex := two_sided_exit_before_ruin_integral_identity X hX q hq W hW a x ha hx0 hxa
  have hexa := two_sided_exit_before_ruin_integral_identity X hX q hq W hW a a ha ha.le (le_refl a)
  refine ⟨hWa, ?_⟩
  rw [hfx, hex, hfa, hexa, div_self hWane, ENNReal.ofReal_one, one_mul]
