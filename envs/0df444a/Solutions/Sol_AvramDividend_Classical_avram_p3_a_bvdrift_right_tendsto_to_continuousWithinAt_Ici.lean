-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_right_tendsto_to_continuousWithinAt_Ici
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:19:57.64545+00:00
-- url     : https://prove2.me/submissions/a9f19b8a-ad79-486b-aaa5-738746bab4c9

import Mathlib.Topology.NhdsWithin
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Strict right convergence gives closed-right continuity on nonnegative time. -/
theorem solution
    (f : ℝ≥0 → ℝ) (t : ℝ≥0)
    (hright : Filter.Tendsto f (𝓝[>] t) (𝓝 (f t))) :
    ContinuousWithinAt f (Ici t) t := by
  have hsplit : (𝓝[Ici t] t) =
      (𝓝[>] t) ⊔ (𝓝[{t}] t) := by
    simpa [nhdsGE] using (nhdsGT_sup_nhdsWithin_singleton t).symm
  change Filter.map f (𝓝[Ici t] t) ≤ 𝓝 (f t)
  rw [hsplit, Filter.map_sup]
  apply sup_le
  · exact hright
  · have hpure : Filter.Tendsto f (pure t) (𝓝 (f t)) :=
      tendsto_pure_nhds f t
    simpa [Filter.Tendsto, nhdsWithin_singleton] using hpure
