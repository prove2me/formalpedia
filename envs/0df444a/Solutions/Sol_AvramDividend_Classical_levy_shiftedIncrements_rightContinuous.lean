-- Prove2me | solution 1 for AvramDividend.Classical.levy_shiftedIncrements_rightContinuous
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T19:17:40.270585+00:00
-- url     : https://prove2.me/submissions/54334247-ae3a-4eef-a669-fb75d79be382

import Mathlib.Topology.Instances.NNReal.Lemmas
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (u : ℝ≥0) :
    ∀ t : ℝ≥0,
      ContinuousWithinAt
        (fun s : ℝ≥0 => X.X (u + s) ω - X.X u ω)
        (Set.Ici t) t := by
  intro t
  have h1 : ContinuousWithinAt (fun s : ℝ≥0 => X.X (u + s) ω) (Set.Ici t) t := by
    have := X.rightCont ω (u + t)
    refine this.comp (continuous_const.add continuous_id).continuousWithinAt ?_
    intro s hs
    exact (add_le_add_iff_left u).2 hs
  exact h1.sub continuousWithinAt_const
