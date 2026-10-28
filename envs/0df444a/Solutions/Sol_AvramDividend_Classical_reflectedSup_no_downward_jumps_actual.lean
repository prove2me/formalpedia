-- Prove2me | solution 1 for AvramDividend.Classical.reflectedSup_no_downward_jumps_actual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T17:40:57.826453+00:00
-- url     : https://prove2.me/submissions/aebbfc5e-99e6-4103-858a-72dda2d6a6f7

import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_left_continuous_actual
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    ∀ (t : ℝ≥0) (l : ℝ), 0 < t →
      Filter.Tendsto (fun s : ℝ≥0 => reflectedSup X s ω)
        (nhdsWithin t (Iio t)) (nhds l) →
      l ≤ reflectedSup X t ω := by
  intro t l ht hR
  obtain ⟨lx, hXleft⟩ := X.leftLim ω t ht
  have hSleft : Tendsto
      (fun s : ℝ≥0 => runningSup X s ω)
      (nhdsWithin t (Iio t)) (nhds (runningSup X t ω)) :=
    runningSup_left_continuous_actual X ω t ht
  have hRleft : Tendsto
      (fun s : ℝ≥0 => runningSup X s ω - X.X s ω)
      (nhdsWithin t (Iio t)) (nhds (runningSup X t ω - lx)) :=
    hSleft.sub hXleft
  haveI : NeBot (nhdsWithin t (Iio t)) :=
    nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  have hLim : l = runningSup X t ω - lx := by
    apply tendsto_nhds_unique hR
    exact hRleft
  change l ≤ runningSup X t ω - X.X t ω
  rw [hLim]
  exact sub_le_sub_left (X.noPosJumps ω t lx ht hXleft) (runningSup X t ω)
