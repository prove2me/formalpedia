-- Prove2me | solution 1 for AvramDividend.Classical.firstRecord_truncation_stopping_rightCont
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:03:18.552019+00:00
-- url     : https://prove2.me/submissions/d6e7ab95-71b8-4bc4-87e0-89f7f02531f9

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_upperPassage_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_extendedStopping_truncate_finite_leEvents

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (M : ℝ≥0) :
    ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s]
        {ω : Ω | (min (twoSidedExitUpTime X b ω) (M : ℝ≥0∞)).toNNReal ≤ s} := by
  exact extendedStopping_truncate_finite_leEvents
    (twoSidedExitUpTime X b)
    (upperPassage_stopping_rightCont_filtration X b) M
