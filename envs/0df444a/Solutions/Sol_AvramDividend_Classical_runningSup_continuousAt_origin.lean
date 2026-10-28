-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_continuousAt_origin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T07:40:39.760978+00:00
-- url     : https://prove2.me/submissions/d99895ee-f866-4c6d-bca9-7b56e845d7e3

import Mathlib.Topology.ContinuousOn
import Mathlib.Data.NNReal.Basic
import Theorems.Thm_AvramDividend_Classical_runningSup_right_continuous_actual
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    ContinuousAt (fun s : ℝ≥0 => runningSup X s ω) 0 := by
  have hright := runningSup_right_continuous_actual X ω 0
  have hset : (Ici (0 : ℝ≥0)) = Set.univ := by
    ext s
    simp
  rw [hset] at hright
  simpa only [continuousWithinAt_univ] using hright
