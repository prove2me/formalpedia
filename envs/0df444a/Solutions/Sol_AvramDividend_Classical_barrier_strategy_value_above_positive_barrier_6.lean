-- Prove2me | solution 6 for AvramDividend.Classical.barrier_strategy_value_above_positive_barrier
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T23:19:42.525959+00:00
-- url     : https://prove2.me/submissions/9526173f-665b-42d4-a138-8696b5c900bf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_above_value_of_boundary
import Theorems.Thm_AvramDividend_Classical_barrierValue_nonnegative_at_nonnegative_barrier
import Theorems.Thm_AvramDividend_Classical_barrierValue_at_positive_barrier_eq_deriv_ratio
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_eq_scale_ratio

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The original policy pays the initial excess and continues from the barrier. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hax : a < x) :
    dividendValue X q x (barrierStrategy X x a) =
      ENNReal.ofReal (barrierValue W a x) := by
  have ha0 : 0 ≤ a := le_of_lt ha
  have hboundary :
      dividendValue X q a (barrierStrategy X a a) =
        ENNReal.ofReal (barrierValue W a a) := by
    rw [barrierValue_at_positive_barrier_eq_deriv_ratio W a ha]
    calc
      dividendValue X q a (barrierStrategy X a a) =
          barrierSupValue X a q :=
        barrierValue_self_eq_barrierSupValue X q a
      _ = ENNReal.ofReal (W a / deriv W a) :=
        barrierSupValue_eq_scale_ratio X hX q hq W hW a ha
  exact barrierStrategy_above_value_of_boundary X q W a x ha0 hax
    hboundary
    (barrierValue_nonnegative_at_nonnegative_barrier X hX q hq W hW a ha0)
