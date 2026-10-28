-- Prove2me | solution 2 for AvramDividend.Classical.runningSup_right_local_const_of_positive_drawdown
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:23:08.919336+00:00
-- url     : https://prove2.me/submissions/38b49862-1f57-4839-a1d1-691bbfde4fa2

import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_const_between_of_path_below_old_record
import Theorems.Thm_AvramDividend_Classical_nnreal_rightContinuous_strict_upper_gap_interval
import Mathlib.Topology.Order.LeftRightNhds

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
  have hgap : X.X u ω < runningSup X u ω := by
    unfold reflectedSup at hPositive; linarith
  obtain ⟨v, huv, hv⟩ := nnreal_rightContinuous_strict_upper_gap_interval (fun s => X.X s ω) u
    (runningSup X u ω) (X.rightCont ω u) hgap
  refine ⟨v, huv, fun t hut htv => ?_⟩
  exact runningSup_const_between_of_path_below_old_record X ω u t hut
    (fun s hus hst => (hv s hus (lt_of_le_of_lt hst htv)).le)
