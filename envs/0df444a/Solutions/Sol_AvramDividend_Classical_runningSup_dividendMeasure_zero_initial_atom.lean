-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_dividendMeasure_zero_initial_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T16:38:57.729083+00:00
-- url     : https://prove2.me/submissions/1650a013-51af-43f9-9236-71aec9e66e4f

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_self_eq_runningSup
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_no_initial_dividendMeasure_atom
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The reflected record's Stieltjes regulator carries no atom at its starting time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a : ℝ) (ha : 0 ≤ a) (ω : Ω) :
    dividendMeasure (runningSup X) ω ({0} : Set ℝ) = 0 := by
  have hfun : barrierStrategy X a a = runningSup X := by
    funext t η
    exact barrierStrategy_self_eq_runningSup X a η t
  rw [← hfun]
  exact barrierStrategy_no_initial_dividendMeasure_atom X a a ha ha (le_refl a) ω
