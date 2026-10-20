-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_realTime_leftLim_eq_pos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T19:41:16.666887+00:00
-- url     : https://prove2.me/submissions/2c9afe02-c93b-49b0-a891-5b722e40c5ff

import Mathlib.Data.NNReal.Defs
import Mathlib.Topology.Order.LeftRightLim
import Theorems.Thm_AvramDividend_Classical_runningSup_left_continuous_actual
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
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
    (r : ℝ) (hr : 0 < r) :
    Function.leftLim
      (fun s : ℝ => runningSup X s.toNNReal ω) r =
      runningSup X r.toNNReal ω := by
  let u : ℝ≥0 := r.toNNReal
  have hu : 0 < u := Real.toNNReal_pos.mpr hr
  have hLeft :
      ContinuousWithinAt
        (fun t : ℝ≥0 => runningSup X t ω) (Set.Iio u) u :=
    runningSup_left_continuous_actual X ω u hu
  have hMaps : Set.MapsTo Real.toNNReal (Set.Iio r) (Set.Iio u) := by
    intro x hx
    exact (Real.toNNReal_lt_toNNReal_iff hr).mpr hx
  have hReal : ContinuousWithinAt
      (fun x : ℝ => runningSup X x.toNNReal ω) (Set.Iio r) r :=
    ContinuousWithinAt.comp
      (f := Real.toNNReal)
      (g := fun t : ℝ≥0 => runningSup X t ω)
      (s := Set.Iio r) (t := Set.Iio u) (x := r)
      hLeft continuous_real_toNNReal.continuousWithinAt hMaps
  have hMono :
      Monotone (fun x : ℝ => runningSup X x.toNNReal ω) := by
    exact (runningSup_monotone_and_path_le X ω).1.comp
      (fun _ _ hxy => Real.toNNReal_mono hxy)
  exact hMono.continuousWithinAt_Iio_iff_leftLim_eq.mp hReal
