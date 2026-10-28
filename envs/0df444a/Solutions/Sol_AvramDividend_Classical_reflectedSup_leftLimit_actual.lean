-- Prove2me | solution 1 for AvramDividend.Classical.reflectedSup_leftLimit_actual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T17:41:11.797532+00:00
-- url     : https://prove2.me/submissions/4283a864-b82e-4631-86f3-52f1ef19e980

import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_left_continuous_actual
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (t : ℝ≥0) (ht : 0 < t) :
    ∃ l : ℝ, Filter.Tendsto
      (fun s : ℝ≥0 => reflectedSup X s ω)
      (nhdsWithin t (Iio t)) (nhds l) := by
  obtain ⟨lx, hXleft⟩ := X.leftLim ω t ht
  have hSleft : Tendsto
      (fun s : ℝ≥0 => runningSup X s ω)
      (nhdsWithin t (Iio t)) (nhds (runningSup X t ω)) :=
    runningSup_left_continuous_actual X ω t ht
  refine ⟨runningSup X t ω - lx, ?_⟩
  exact hSleft.sub hXleft
