-- Prove2me | solution 13 for AvramDividend.Classical.barrier_value_scale_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T08:06:05.389992+00:00
-- url     : https://prove2.me/submissions/debe86ec-1184-4dc8-afb5-4608cc4575d5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_value_eq_exit_factor
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue
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
  have hWpos : 0 < W a :=
    AvramDividend.Classical.scaleFunction_strict_pos_of_standing X hX q hq W hW a ha
  refine ⟨hWpos, ?_⟩
  have hExit :=
    AvramDividend.Classical.barrierStrategy_value_eq_exit_factor X hX q hq W hW a ha x hx0 hxa
  have hSelf :=
    AvramDividend.Classical.barrierValue_self_eq_barrierSupValue X q a
  rw [hSelf]
  exact hExit
