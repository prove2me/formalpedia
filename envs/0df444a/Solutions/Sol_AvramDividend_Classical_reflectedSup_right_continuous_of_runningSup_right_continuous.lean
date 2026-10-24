-- Prove2me | solution 1 for AvramDividend.Classical.reflectedSup_right_continuous_of_runningSup_right_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T10:59:23.789212+00:00
-- url     : https://prove2.me/submissions/09226119-c32e-43fb-bc50-b81953204e7a

import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_reflectedSup_right_continuous
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Defs.Filter

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! Unconditional reflected-path right continuity discharges the conditional form. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (u : ℝ≥0)
    (hSup : ContinuousWithinAt (fun t : ℝ≥0 => runningSup X t ω)
      (Set.Ici u) u) :
    ContinuousWithinAt (fun t : ℝ≥0 => reflectedSup X t ω)
      (Set.Ici u) u := by
  exact AvramDividend.Classical.reflectedSup_right_continuous X ω u
