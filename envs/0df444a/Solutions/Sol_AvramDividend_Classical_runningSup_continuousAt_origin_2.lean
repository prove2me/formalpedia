-- Prove2me | solution 2 for AvramDividend.Classical.runningSup_continuousAt_origin
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T07:40:45.225844+00:00
-- url     : https://prove2.me/submissions/5346c3ac-5966-4c6a-ad01-9b1459ea9670

import Mathlib.Topology.ContinuousOn
import Mathlib.Data.NNReal.Basic
import Theorems.Thm_AvramDividend_Classical_runningSup_right_continuous_actual

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    ContinuousAt (fun s : ℝ≥0 => runningSup X s ω) 0 := by
  have h := runningSup_right_continuous_actual X ω 0
  have hI : Set.Ici (0 : ℝ≥0) = Set.univ := by ext; simp
  rw [hI, continuousWithinAt_univ] at h
  exact h
