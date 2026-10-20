-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_realTime_rightLim_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T18:14:44.229298+00:00
-- url     : https://prove2.me/submissions/637f330b-f8fd-436d-9690-1ddcd4c4fe27

import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_reflectedSup_right_continuous

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (r : ℝ) :
    Function.rightLim
        (fun s : ℝ => runningSup X s.toNNReal ω) r =
      runningSup X r.toNNReal ω := by
  let u : ℝ≥0 := r.toNNReal
  have hAdd : ContinuousWithinAt
      (fun t : ℝ≥0 => reflectedSup X t ω + X.X t ω)
      (Set.Ici u) u :=
    (reflectedSup_right_continuous X ω u).add (X.rightCont ω u)
  have hSup : ContinuousWithinAt
      (fun t : ℝ≥0 => runningSup X t ω)
      (Set.Ici u) u := by
    simpa only [reflectedSup, sub_add_cancel] using hAdd
  have hMaps : Set.MapsTo Real.toNNReal
      (Set.Ici r) (Set.Ici u) := by
    intro t ht
    exact Real.toNNReal_mono ht
  have hReal : ContinuousWithinAt
      (fun t : ℝ => runningSup X t.toNNReal ω)
      (Set.Ici r) r :=
    ContinuousWithinAt.comp
      (f := Real.toNNReal)
      (g := fun t : ℝ≥0 => runningSup X t ω)
      (s := Set.Ici r) (t := Set.Ici u) (x := r)
      hSup continuous_real_toNNReal.continuousWithinAt hMaps
  exact hReal.rightLim_eq
