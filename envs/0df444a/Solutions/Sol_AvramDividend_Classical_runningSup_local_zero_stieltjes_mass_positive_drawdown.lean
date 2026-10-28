-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_local_zero_stieltjes_mass_positive_drawdown
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T00:28:32.267372+00:00
-- url     : https://prove2.me/submissions/14855aa0-c069-4ebc-b277-92d5ae271e6d

import Definitions.Def_AvramDividend_Classical_Reflection
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_runningSup_no_new_record_interval_zero_stieltjes_mass
import Theorems.Thm_AvramDividend_Classical_nnreal_rightContinuous_strict_upper_gap_interval
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (u : ℝ≥0)
    (hPositive : 0 < reflectedSup X u ω) :
    ∃ v : ℝ≥0, u < v ∧
      (dividendMeasure (runningSup X) ω)
        (Set.Ioc (u : ℝ) (v : ℝ)) = 0 := by
  have hGap : X.X u ω < runningSup X u ω := by
    change 0 < runningSup X u ω - X.X u ω at hPositive
    exact sub_pos.mp hPositive
  obtain ⟨v, huv, hBelow⟩ :=
    nnreal_rightContinuous_strict_upper_gap_interval
      (fun t : ℝ≥0 => X.X t ω)
      u (runningSup X u ω) (X.rightCont ω u) hGap
  obtain ⟨w, huw, hwv⟩ := exists_between huv
  refine ⟨w, huw, ?_⟩
  apply runningSup_no_new_record_interval_zero_stieltjes_mass
    X ω u w huw.le
  intro t hut htw
  exact (hBelow t hut (lt_of_le_of_lt htw hwv)).le
