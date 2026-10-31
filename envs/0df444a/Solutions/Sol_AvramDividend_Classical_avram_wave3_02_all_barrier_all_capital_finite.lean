-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_all_barrier_all_capital_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T08:17:14.002992+00:00
-- url     : https://prove2.me/submissions/2864d63e-8d39-43bb-920d-3a9f5df8edeb

import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_standing_barrierSupValue_lt_top
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_value_eq_exit_factor
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_above_value_eq_initial_excess_sup
import Theorems.Thm_AvramDividend_Classical_barrier_strategy_value_zero_all_capital
import Mathlib.Data.ENNReal.Operations
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- True controlled-barrier discounted dividends have finite expectation at
every nonnegative reserve and every nonnegative barrier, without scale C1. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 ≤ a) (hx : 0 ≤ x) :
    dividendValue X q x (barrierStrategy X x a) < ⊤ := by
  by_cases hz : a = 0
  · subst a
    have hv := barrier_strategy_value_zero_all_capital X hX q hq W hW x hx
    rw [hv]
    exact ENNReal.ofReal_lt_top
  · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm hz)
    have hsup : barrierSupValue X a q < ⊤ :=
      avram_wave3_02_standing_barrierSupValue_lt_top
        X hX q hq W hW a ha_pos
    by_cases hxa : x ≤ a
    · rw [barrierStrategy_value_eq_exit_factor X hX q hq W hW
        a ha_pos x hx hxa]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hsup
    · have hax : a < x := lt_of_not_ge hxa
      rw [avram_wave3_02_above_value_eq_initial_excess_sup X q a x ha hax]
      exact ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, hsup⟩
