-- Prove2me | solution 2 for AvramDividend.Classical.runningSup_continuous_actual
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T07:49:29.392408+00:00
-- url     : https://prove2.me/submissions/532b794a-bb92-40bf-98a5-1d92d11cb0d8

import Mathlib.Topology.ContinuousOn
import Theorems.Thm_AvramDividend_Classical_runningSup_continuousAt_positive
import Theorems.Thm_AvramDividend_Classical_runningSup_continuousAt_origin

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    Continuous (fun t : ℝ≥0 => runningSup X t ω) := by
  refine continuous_iff_continuousAt.2 fun t => ?_
  rcases eq_or_ne t 0 with rfl | ht
  · exact runningSup_continuousAt_origin X ω
  · exact runningSup_continuousAt_positive X ω t (pos_iff_ne_zero.2 ht)
