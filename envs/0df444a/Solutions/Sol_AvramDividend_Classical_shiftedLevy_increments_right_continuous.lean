-- Prove2me | solution 1 for AvramDividend.Classical.shiftedLevy_increments_right_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T14:26:42.13856+00:00
-- url     : https://prove2.me/submissions/61f48ac6-cc73-44ae-8962-59da83c83318

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.ContinuousOn

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- A fixed shift and subtraction preserve right-continuity of a Levy path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (u : ℝ≥0) :
    ∀ t : ℝ≥0,
      ContinuousWithinAt
        (fun r : ℝ≥0 => X.X (u + r) ω - X.X u ω)
        (Set.Ici t) t := by
  intro t
  have hshift :
      ContinuousWithinAt (fun r : ℝ≥0 => u + r) (Set.Ici t) t :=
    (continuous_const.add continuous_id).continuousWithinAt
  have hmap : Set.MapsTo (fun r : ℝ≥0 => u + r)
      (Set.Ici t) (Set.Ici (u + t)) := by
    intro r hr
    change u + t ≤ u + r
    calc
      u + t = t + u := add_comm u t
      _ ≤ r + u := add_le_add_left hr u
      _ = u + r := add_comm r u
  have hpath :
      ContinuousWithinAt (fun r : ℝ≥0 => X.X (u + r) ω) (Set.Ici t) t := by
    change ContinuousWithinAt ((fun s : ℝ≥0 => X.X s ω) ∘
      (fun r : ℝ≥0 => u + r)) (Set.Ici t) t
    exact (X.rightCont ω (u + t)).comp hshift hmap
  have hconst :
      ContinuousWithinAt (fun _ : ℝ≥0 => X.X u ω) (Set.Ici t) t :=
    continuousWithinAt_const
  exact hpath.sub hconst
