-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_right_local_const_of_positive_drawdown
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T00:23:03.979645+00:00
-- url     : https://prove2.me/submissions/7e8cb71b-74b0-4138-ab9f-f7edaf9981b8

import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_const_between_of_path_below_old_record
import Theorems.Thm_AvramDividend_Classical_nnreal_rightContinuous_strict_upper_gap_interval
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Topology Filter
open scoped NNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (u : ℝ≥0)
    (hPositive : 0 < reflectedSup X u ω) :
    ∃ v : ℝ≥0, u < v ∧
      ∀ t : ℝ≥0, u ≤ t → t < v →
        runningSup X t ω = runningSup X u ω := by
  have hGap : X.X u ω < runningSup X u ω := by
    change 0 < runningSup X u ω - X.X u ω at hPositive
    exact sub_pos.mp hPositive
  obtain ⟨v, huv, hPath⟩ :=
    nnreal_rightContinuous_strict_upper_gap_interval
      (fun t : ℝ≥0 => X.X t ω)
      u (runningSup X u ω) (X.rightCont ω u) hGap
  refine ⟨v, huv, ?_⟩
  intro t hut htv
  apply runningSup_const_between_of_path_below_old_record X ω u t hut
  intro w huw hwt
  exact (hPath w huw (lt_of_le_of_lt hwt htv)).le
