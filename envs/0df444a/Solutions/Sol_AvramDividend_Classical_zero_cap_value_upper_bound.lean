-- Prove2me | solution 1 for AvramDividend.Classical.zero_cap_value_upper_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T18:40:01.251994+00:00
-- url     : https://prove2.me/submissions/fc5e0748-de14-45e8-9670-3542a298f67c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_zero_cap_value_at_zero_upper_bound
import Theorems.Thm_AvramDividend_Classical_barrier_strategy_value_zero_all_capital
import Theorems.Thm_AvramDividend_Classical_valueFunctionLe_above_cap
import Theorems.Thm_AvramDividend_Classical_add_initial_excess_admissible_value
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_eq_add_initial_excess_above_barrier
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_left_continuous
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_continuous
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_adapted
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_capped_admissible_of_regular

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q 0 x ≤ ENNReal.ofReal (barrierValue W 0 x) := by
  have hbar0 :
      IsAdmissibleLe X 0 (ENNReal.ofReal 0) (barrierStrategy X 0 0) := by
    simpa using
      AvramDividend.Classical.barrierStrategy_capped_admissible_of_regular
        X 0 (le_refl 0)
        (AvramDividend.Classical.barrierStrategy_left_continuous X 0)
        (AvramDividend.Classical.barrierStrategy_right_continuous X 0)
        (AvramDividend.Classical.barrierStrategy_adapted X 0)
  have hbound0 :=
    AvramDividend.Classical.zero_cap_value_at_zero_upper_bound
      X hX q hq W hW
  have hvalue0 :=
    AvramDividend.Classical.barrier_strategy_value_zero_all_capital
      X hX q hq W hW 0 (le_refl 0)
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    exact hbound0
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    have habove :=
      AvramDividend.Classical.valueFunctionLe_above_cap
        X q x 0 (le_refl 0) hxpos
    have hadd :=
      AvramDividend.Classical.add_initial_excess_admissible_value
        X q x 0 (le_refl 0) hxpos (barrierStrategy X 0 0)
        (by simpa only [ENNReal.ofReal_zero] using hbar0)
    have hstrategy :=
      AvramDividend.Classical.barrierStrategy_eq_add_initial_excess_above_barrier
        X x 0 (le_refl 0) hxpos
    have hvaluex :=
      AvramDividend.Classical.barrier_strategy_value_zero_all_capital
        X hX q hq W hW x hx
    calc
      valueFunctionLe X q 0 x =
          ENNReal.ofReal (x - 0) + valueFunctionLe X q 0 0 := by
        simpa using habove
      _ ≤ ENNReal.ofReal (x - 0) +
            ENNReal.ofReal (barrierValue W 0 0) := by
        simpa [add_comm] using
          add_le_add_left hbound0 (ENNReal.ofReal (x - 0))
      _ = ENNReal.ofReal (x - 0) +
            dividendValue X q 0 (barrierStrategy X 0 0) := by
        rw [hvalue0]
      _ = dividendValue X q x (barrierStrategy X x 0) := by
        rw [hstrategy]
        exact hadd.2.symm
      _ = ENNReal.ofReal (barrierValue W 0 x) := hvaluex
