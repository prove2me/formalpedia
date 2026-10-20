-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_dividendMeasure_no_real_atoms
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T20:50:11.409029+00:00
-- url     : https://prove2.me/submissions/bdd17334-4d61-44d1-b879-58fa583b50b9

import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_no_negative_atoms
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_no_nonnegative_atoms
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (t : ℝ) :
    (dividendMeasure (runningSup X) ω) ({t} : Set ℝ) = 0 := by
  rcases lt_or_ge t 0 with ht | ht
  · exact runningSup_dividendMeasure_no_negative_atoms X ω t ht
  · exact runningSup_dividendMeasure_no_nonnegative_atoms X ω t ht
