-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_all_barrier_positive_capital_pos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T08:23:05.181281+00:00
-- url     : https://prove2.me/submissions/da97bd8c-abd0-4294-9ab6-e69cb712b4b1

import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_standing_barrierSupValue_pos
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_value_eq_exit_factor
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_above_value_eq_initial_excess_sup
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_all_nonnegative_barriers_sup
import Mathlib.Data.ENNReal.Operations
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Genuine barrier dividends have strictly positive discounted expectation at
any positive initial reserve, for every nonnegative cap and without scale C1. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 ≤ a) (hx : 0 < x) :
    0 < dividendValue X q x (barrierStrategy X x a) := by
  by_cases hz : a = 0
  · subst a
    have hv := avram_wave3_02_all_nonnegative_barriers_sup
      X hX q hq W hW 0 le_rfl x (le_of_lt hx)
    simp only [if_pos rfl] at hv
    rw [hv]
    exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hx)
      (le_add_of_nonneg_right bot_le)
  · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm hz)
    by_cases hxa : x ≤ a
    · have hWx : 0 < W x :=
        scaleFunction_strict_pos_of_standing X hX q hq W hW x hx
      have hWa : 0 < W a :=
        scaleFunction_strict_pos_of_standing X hX q hq W hW a ha_pos
      have hs : 0 < barrierSupValue X a q :=
        avram_wave3_02_standing_barrierSupValue_pos X hX q hq W hW a ha_pos
      rw [barrierStrategy_value_eq_exit_factor X hX q hq W hW
        a ha_pos x (le_of_lt hx) hxa]
      exact ENNReal.mul_pos
        (ne_of_gt (ENNReal.ofReal_pos.mpr (div_pos hWx hWa))) (ne_of_gt hs)
    · have hax : a < x := lt_of_not_ge hxa
      rw [avram_wave3_02_above_value_eq_initial_excess_sup X q a x ha hax]
      exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (sub_pos.mpr hax))
        (le_add_of_nonneg_right bot_le)
