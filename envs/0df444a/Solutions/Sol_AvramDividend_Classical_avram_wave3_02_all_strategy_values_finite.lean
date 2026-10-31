-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_all_strategy_values_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T13:32:53.381316+00:00
-- url     : https://prove2.me/submissions/9e00684c-faa4-4804-ac54-6d30329d0ae4

import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_uniform_strategy_value_growth
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Every genuine barrier strategy has finite expected discounted Stieltjes
    dividends, at every nonnegative cap and initial capital. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∀ (a x : ℝ), 0 ≤ a → 0 ≤ x →
      dividendValue X q x (barrierStrategy X x a) < ∞ := by
  obtain ⟨C, hC, hbound⟩ :=
    avram_wave3_02_uniform_strategy_value_growth X hX q hq W hW
  intro a x ha hx
  calc
    dividendValue X q x (barrierStrategy X x a) ≤
        ENNReal.ofReal x + ENNReal.ofReal C := hbound a x ha hx
    _ < ∞ := by simp
