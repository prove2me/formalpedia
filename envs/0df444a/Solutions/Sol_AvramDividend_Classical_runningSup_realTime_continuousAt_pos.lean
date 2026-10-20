-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_realTime_continuousAt_pos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T19:52:30.244032+00:00
-- url     : https://prove2.me/submissions/1985ce9d-44bc-490c-814e-d265df346c61

import Mathlib.Topology.Order.LeftRightLim
import Theorems.Thm_AvramDividend_Classical_runningSup_realTime_leftLim_eq_pos
import Theorems.Thm_AvramDividend_Classical_runningSup_realTime_rightLim_eq
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (t : ℝ) (ht : 0 < t) :
    ContinuousAt (fun r : ℝ => runningSup X r.toNNReal ω) t := by
  have hMono :
      Monotone (fun r : ℝ => runningSup X r.toNNReal ω) :=
    (runningSup_monotone_and_path_le X ω).1.comp
      (fun _ _ hxy => Real.toNNReal_mono hxy)
  apply hMono.continuousAt_iff_leftLim_eq_rightLim.mpr
  rw [runningSup_realTime_leftLim_eq_pos X ω t ht,
      runningSup_realTime_rightLim_eq X ω t]
