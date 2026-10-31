-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_value_monotone_in_initial_capital
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T08:26:27.219307+00:00
-- url     : https://prove2.me/submissions/f7c189f7-2127-40a3-b66b-785aa0f45b15

import Mathlib.Data.ENNReal.Real
import Mathlib.Algebra.Order.Field.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_all_nonnegative_barriers_sup
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_value_eq_exit_factor
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_above_value_eq_initial_excess_sup
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- True discounted Stieltjes barrier dividend value is monotone in initial
capital for every nonnegative barrier, without any differentiability of W. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 ≤ a) :
    MonotoneOn (fun x : ℝ =>
      dividendValue X q x (barrierStrategy X x a)) (Ici 0) := by
  intro x hx y hy hxy
  change dividendValue X q x (barrierStrategy X x a) ≤
    dividendValue X q y (barrierStrategy X y a)
  have hx0 : 0 ≤ x := hx
  have hy0 : 0 ≤ y := hy
  by_cases hz : a = 0
  · subst a
    have hvx := avram_wave3_02_all_nonnegative_barriers_sup
      X hX q hq W hW 0 le_rfl x hx0
    have hvy := avram_wave3_02_all_nonnegative_barriers_sup
      X hX q hq W hW 0 le_rfl y hy0
    simp only [if_pos rfl] at hvx hvy
    rw [hvx, hvy]
    simpa [add_comm] using
      (add_le_add_right (ENNReal.ofReal_le_ofReal hxy)
        (barrierSupValue X 0 q))
  · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm hz)
    have hWa : 0 < W a :=
      scaleFunction_strict_pos_of_standing X hX q hq W hW a ha_pos
    by_cases hybar : y ≤ a
    · have hxbar : x ≤ a := le_trans hxy hybar
      rw [barrierStrategy_value_eq_exit_factor X hX q hq W hW
        a ha_pos x hx0 hxbar]
      rw [barrierStrategy_value_eq_exit_factor X hX q hq W hW
        a ha_pos y hy0 hybar]
      have hscale : W x ≤ W y :=
        scaleFunction_monotone X q W hW hxy
      have hfrac : W x / W a ≤ W y / W a :=
        (div_le_div_iff_of_pos_right hWa).2 hscale
      exact mul_le_mul_of_nonneg_right
        (ENNReal.ofReal_le_ofReal hfrac) bot_le
    · have hay : a < y := lt_of_not_ge hybar
      by_cases hxbar : x ≤ a
      · have hscale : W x ≤ W a :=
          scaleFunction_monotone X q W hW hxbar
        have hfrac : W x / W a ≤ 1 :=
          (div_le_iff₀ hWa).2 (by simpa using hscale)
        have hfac : ENNReal.ofReal (W x / W a) ≤ 1 := by
          simpa using (ENNReal.ofReal_le_ofReal hfrac)
        calc
          dividendValue X q x (barrierStrategy X x a) =
              ENNReal.ofReal (W x / W a) * barrierSupValue X a q :=
                barrierStrategy_value_eq_exit_factor
                  X hX q hq W hW a ha_pos x hx0 hxbar
          _ ≤ 1 * barrierSupValue X a q :=
                mul_le_mul_of_nonneg_right hfac bot_le
          _ = barrierSupValue X a q := one_mul _
          _ ≤ ENNReal.ofReal (y - a) + barrierSupValue X a q :=
                le_add_of_nonneg_left bot_le
          _ = dividendValue X q y (barrierStrategy X y a) :=
                (avram_wave3_02_above_value_eq_initial_excess_sup X q a y ha hay).symm
      · have hax : a < x := lt_of_not_ge hxbar
        rw [avram_wave3_02_above_value_eq_initial_excess_sup X q a x ha hax]
        rw [avram_wave3_02_above_value_eq_initial_excess_sup X q a y ha hay]
        simpa [add_comm] using
          (add_le_add_right
            (ENNReal.ofReal_le_ofReal (sub_le_sub_right hxy a))
            (barrierSupValue X a q))
