-- Prove2me | solution 15 for AvramDividend.Classical.barrier_strategy_value
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:58:36.310148+00:00
-- url     : https://prove2.me/submissions/2c38f7e7-fb7e-420d-9a7b-665db03eb182
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_value_eq_killed_exit_mul_supValue
import Theorems.Thm_AvramDividend_Classical_two_sided_exit_before_ruin_integral_identity
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_eq_scale_ratio
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
    dividendValue X q x (barrierStrategy X x a) = ENNReal.ofReal (W x / deriv W a) := by
  have hWa : 0 < W a := scaleFunction_strict_pos_of_standing X hX q hq W hW a ha
  have hWnn : ∀ y : ℝ, 0 ≤ y → 0 ≤ W y := hW.2.1
  have hfactor := barrierStrategy_value_eq_killed_exit_mul_supValue X hX q hq a x ha hx0 hxa
  have hexit := two_sided_exit_before_ruin_integral_identity X hX q hq W hW a x ha hx0 hxa
  have hsup := barrierSupValue_eq_scale_ratio X hX q hq W hW a ha
  rw [hfactor, hexit, hsup, ← ENNReal.ofReal_mul (div_nonneg (hWnn x hx0) hWa.le)]
  congr 1
  by_cases hd : deriv W a = 0
  · simp [hd, div_zero, mul_zero]
  · have hWane : W a ≠ 0 := ne_of_gt hWa
    field_simp
