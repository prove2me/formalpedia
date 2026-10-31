-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_barrier_value_all_capital_of_pointwise_diff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T13:12:32.55382+00:00
-- url     : https://prove2.me/submissions/0868bf71-83fc-4e54-9fb1-a0ace966283d

import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_barrier_value_of_pointwise_diff
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_above_value_eq_initial_excess_sup
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_ratio_of_pointwise_diff_and_sandwich
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Exact original barrier strategy value at all starting reserves for a
positive barrier where the q-scale function is differentiable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x)
    (hda : DifferentiableAt ℝ W a) :
    dividendValue X q x (barrierStrategy X x a) =
      if x ≤ a then ENNReal.ofReal (W x / deriv W a)
      else ENNReal.ofReal (x - a) + ENNReal.ofReal (W a / deriv W a) := by
  by_cases hxa : x ≤ a
  · rw [if_pos hxa]
    exact avram_wave3_02_barrier_value_of_pointwise_diff
      X hX q hq W hW a x ha hx0 hxa hda
  · rw [if_neg hxa]
    have hax : a < x := lt_of_not_ge hxa
    rw [avram_wave3_02_above_value_eq_initial_excess_sup
      X q a x (le_of_lt ha) hax]
    rw [avram_wave3_02_ratio_of_pointwise_diff_and_sandwich
      X hX q hq W hW a ha hda]
