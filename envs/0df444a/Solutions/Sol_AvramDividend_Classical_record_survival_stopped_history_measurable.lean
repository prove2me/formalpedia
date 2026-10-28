-- Prove2me | solution 1 for AvramDividend.Classical.record_survival_stopped_history_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T21:59:07.221993+00:00
-- url     : https://prove2.me/submissions/5e6929a7-6e4c-4b1c-a473-f75bdfc756f1

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_upperPassage_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_stopping_rightCont_filtration

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a b : ℝ) :
    MeasurableSet[(upperPassage_stopping_rightCont_filtration X b).measurableSpace]
      {ω : Ω | twoSidedExitUpTime X b ω < barrierRuinTime X a ω} := by
  let hτ := upperPassage_stopping_rightCont_filtration X b
  let hT := barrierRuinTime_stopping_rightCont_filtration X a
  have hle : MeasurableSet[hτ.measurableSpace]
      {ω : Ω | barrierRuinTime X a ω ≤ twoSidedExitUpTime X b ω} := by
    exact hT.measurableSet_stopping_time_le hτ
  convert hle.compl using 1
  ext ω
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
