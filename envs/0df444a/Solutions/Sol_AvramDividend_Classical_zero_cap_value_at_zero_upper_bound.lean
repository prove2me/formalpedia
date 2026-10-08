-- Prove2me | solution 1 for AvramDividend.Classical.zero_cap_value_at_zero_upper_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T18:03:59.096968+00:00
-- url     : https://prove2.me/submissions/6569c7ae-5cf4-4681-9d2b-a909a918bf94
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_zero_cap_admissible_dividendValue_le_barrier_at_zero
import Theorems.Thm_AvramDividend_Classical_barrier_strategy_value_zero_all_capital

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    valueFunctionLe X q 0 0 ≤ ENNReal.ofReal (barrierValue W 0 0) := by
  rw [valueFunctionLe]
  refine iSup_le ?_
  intro D
  refine iSup_le ?_
  intro hD
  calc
    dividendValue X q 0 D
        ≤ dividendValue X q 0 (barrierStrategy X 0 0) :=
      zero_cap_admissible_dividendValue_le_barrier_at_zero X hX q hq D hD
    _ = ENNReal.ofReal (barrierValue W 0 0) :=
      barrier_strategy_value_zero_all_capital X hX q hq W hW 0 le_rfl
