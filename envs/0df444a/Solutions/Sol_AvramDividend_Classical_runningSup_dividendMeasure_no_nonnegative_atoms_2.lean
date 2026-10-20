-- Prove2me | solution 2 for AvramDividend.Classical.runningSup_dividendMeasure_no_nonnegative_atoms
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T20:29:35.029205+00:00
-- url     : https://prove2.me/submissions/b0c4d564-f4d0-4d31-962a-317542ec730a

import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_zero_atom
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_no_positive_atoms

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (t : ℝ) (ht : 0 ≤ t) :
    (dividendMeasure (runningSup X) ω) ({t} : Set ℝ) = 0 := by
  rcases eq_or_lt_of_le ht with h0 | hp
  · rw [← h0]
    exact runningSup_dividendMeasure_zero_atom X ω
  · exact runningSup_dividendMeasure_no_positive_atoms X ω t hp
