-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_continuous_actual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T07:48:47.410874+00:00
-- url     : https://prove2.me/submissions/d94a882d-b2e7-409f-9572-6f0dd935e32c

import Mathlib.Topology.ContinuousOn
import Theorems.Thm_AvramDividend_Classical_runningSup_continuousAt_positive
import Theorems.Thm_AvramDividend_Classical_runningSup_continuousAt_origin
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
    Continuous (fun t : ℝ≥0 => runningSup X t ω) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  by_cases ht : t = 0
  · subst t
    exact runningSup_continuousAt_origin X ω
  · have hpos : 0 < t := pos_iff_ne_zero.mpr ht
    exact runningSup_continuousAt_positive X ω t hpos
