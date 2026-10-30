-- Prove2me | solution 3 for AvramDividend.Classical.barrierStrategy_cstar_value_all_capital
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T23:19:56.17555+00:00
-- url     : https://prove2.me/submissions/77023c49-2984-4859-ba39-458133f440f2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrier_strategy_value_zero_all_capital
import Theorems.Thm_AvramDividend_Classical_barrier_strategy_value
import Theorems.Thm_AvramDividend_Classical_barrier_strategy_value_above_positive_barrier

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The original cstar regulator pays its exact scale value at every initial reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) :
    ∀ x : ℝ, 0 ≤ x →
      dividendValue X q x (barrierStrategy X x (cstar W).toReal) =
        ENNReal.ofReal (vcstar W x) := by
  intro x hx
  have ha0 : 0 ≤ (cstar W).toReal := ENNReal.toReal_nonneg
  by_cases hzero : (cstar W).toReal = 0
  · simpa [vcstar, hzero] using
      (barrier_strategy_value_zero_all_capital X hX q hq W hW x hx)
  · have hapos : 0 < (cstar W).toReal :=
      lt_of_le_of_ne ha0 (Ne.symm hzero)
    by_cases hxa : x ≤ (cstar W).toReal
    · have hval :=
        barrier_strategy_value X hX q hq W hW
          (cstar W).toReal hapos x hx hxa
      have hxnot : ¬ x < 0 := by linarith
      simpa [vcstar, barrierValue, scaleDeriv, divE, hxnot, hxa, hzero] using hval
    · have hax : (cstar W).toReal < x := lt_of_not_ge hxa
      simpa [vcstar] using
        (barrier_strategy_value_above_positive_barrier X hX q hq W hW
          (cstar W).toReal x hapos hax)
