-- Prove2me | solution 2 for AvramDividend.Classical.barrier_strategy_value_all_capital_nonnegative_barrier
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T13:34:41.934023+00:00
-- url     : https://prove2.me/submissions/7452b97b-45c1-490f-be46-26721fdc74b2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrier_strategy_value
import Theorems.Thm_AvramDividend_Classical_barrier_strategy_value_zero_all_capital
import Theorems.Thm_AvramDividend_Classical_barrier_strategy_value_above_positive_barrier

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 ≤ a) (hx : 0 ≤ x) :
    dividendValue X q x (barrierStrategy X x a) =
      ENNReal.ofReal (barrierValue W a x) := by
  by_cases ha0 : a = 0
  · subst a
    exact AvramDividend.Classical.barrier_strategy_value_zero_all_capital
      X hX q hq W hW x hx
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    by_cases hxa : x ≤ a
    · have hval :=
        AvramDividend.Classical.barrier_strategy_value
          X hX q hq W hW a hapos x hx hxa
      have hxnot : ¬ x < 0 := by linarith
      simpa [barrierValue, scaleDeriv, divE, hxnot, hxa, ha0] using hval
    · have hax : a < x := lt_of_not_ge hxa
      exact AvramDividend.Classical.barrier_strategy_value_above_positive_barrier
        X hX q hq W hW a x hapos hax
