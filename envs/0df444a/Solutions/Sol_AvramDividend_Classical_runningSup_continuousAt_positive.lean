-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_continuousAt_positive
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T07:38:05.117528+00:00
-- url     : https://prove2.me/submissions/0cba36a3-3c64-437f-92d1-c42214152430

import Mathlib.Topology.Order.LeftRight
import Theorems.Thm_AvramDividend_Classical_runningSup_left_continuous_actual
import Theorems.Thm_AvramDividend_Classical_runningSup_right_continuous_actual

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (t : ℝ≥0) (ht : 0 < t) :
    ContinuousAt (fun s : ℝ≥0 => runningSup X s ω) t := by
  exact continuousAt_iff_continuous_left'_right'.2
    ⟨runningSup_left_continuous_actual X ω t ht,
      (runningSup_right_continuous_actual X ω t).mono Set.Ioi_subset_Ici_self⟩
