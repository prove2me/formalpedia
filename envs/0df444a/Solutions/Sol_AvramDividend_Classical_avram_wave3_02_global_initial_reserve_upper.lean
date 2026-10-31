-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_global_initial_reserve_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T08:20:45.449807+00:00
-- url     : https://prove2.me/submissions/131621c9-2d72-4a51-99b4-aaa471e45708

import Mathlib.Data.ENNReal.Basic
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
import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The actual discounted dividend reward from any initial reserve is bounded
by the reserve itself plus the genuine reflected boundary reward, without C1. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 ≤ a) (hx : 0 ≤ x) :
    dividendValue X q x (barrierStrategy X x a) ≤
      ENNReal.ofReal x + barrierSupValue X a q := by
  by_cases hz : a = 0
  · subst a
    exact le_of_eq (by simpa using
      (avram_wave3_02_all_nonnegative_barriers_sup
        X hX q hq W hW 0 le_rfl x hx))
  · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm hz)
    by_cases hxa : x ≤ a
    · have hWa_pos : 0 < W a :=
        scaleFunction_strict_pos_of_standing X hX q hq W hW a ha_pos
      have hWx_le : W x ≤ W a :=
        scaleFunction_monotone X q W hW hxa
      have hfrac_le : W x / W a ≤ 1 :=
        (div_le_iff₀ hWa_pos).2 (by simpa using hWx_le)
      have hfac : ENNReal.ofReal (W x / W a) ≤ 1 := by
        simpa using (ENNReal.ofReal_le_ofReal hfrac_le)
      rw [barrierStrategy_value_eq_exit_factor X hX q hq W hW
        a ha_pos x hx hxa]
      calc
        ENNReal.ofReal (W x / W a) * barrierSupValue X a q ≤
            1 * barrierSupValue X a q :=
              mul_le_mul_of_nonneg_right hfac bot_le
        _ = barrierSupValue X a q := one_mul _
        _ ≤ ENNReal.ofReal x + barrierSupValue X a q :=
              le_add_of_nonneg_left bot_le
    · have hax : a < x := lt_of_not_ge hxa
      rw [avram_wave3_02_above_value_eq_initial_excess_sup X q a x ha hax]
      have hxminus : x - a ≤ x := by linarith
      simpa [add_comm] using
        (add_le_add_right (ENNReal.ofReal_le_ofReal hxminus)
          (barrierSupValue X a q))
