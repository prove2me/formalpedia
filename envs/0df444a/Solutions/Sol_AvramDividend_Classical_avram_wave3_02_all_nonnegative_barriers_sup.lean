-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_all_nonnegative_barriers_sup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T00:55:57.561926+00:00
-- url     : https://prove2.me/submissions/8b9b4021-2723-4eaf-b3f7-d5507e1fd26b

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_piecewise_all_capital_sup
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_above_value_eq_initial_excess_sup
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- A single genuine all-capital reflected-value decomposition for every
nonnegative barrier, including zero, with no scale smoothness assumption. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 ≤ a) :
    ∀ x : ℝ, 0 ≤ x →
      dividendValue X q x (barrierStrategy X x a) =
        if a = 0 then ENNReal.ofReal x + barrierSupValue X a q
        else if x ≤ a then
          ENNReal.ofReal (W x / W a) * barrierSupValue X a q
        else ENNReal.ofReal (x - a) + barrierSupValue X a q := by
  intro x hx
  by_cases hzero : a = 0
  · simp only [if_pos hzero]
    subst a
    by_cases hxzero : x = 0
    · subst x
      simpa using (barrierValue_self_eq_barrierSupValue X q 0)
    · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hxzero)
      simpa using (avram_wave3_02_above_value_eq_initial_excess_sup
        X q 0 x le_rfl hxpos)
  · simp only [if_neg hzero]
    have haPos : 0 < a := lt_of_le_of_ne ha (Ne.symm hzero)
    exact avram_wave3_02_piecewise_all_capital_sup
      X hX q hq W hW a haPos x hx
