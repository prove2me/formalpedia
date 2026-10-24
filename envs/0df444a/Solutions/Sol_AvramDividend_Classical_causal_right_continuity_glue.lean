-- Prove2me | solution 1 for AvramDividend.Classical.causal_right_continuity_glue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T07:33:54.860352+00:00
-- url     : https://prove2.me/submissions/b9ffea90-6b85-4bb9-a463-eaa3935459ef

import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.ContinuousOn
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Set Filter
open scoped Topology

/-- Positive-time continuity and the right limit give continuity at the boundary. -/
theorem solution
    (F : ℝ → ℝ)
    (hpositive : ContinuousOn F (Ioi (0 : ℝ)))
    (horigin : Tendsto F (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ))) (nhds (F 0))) :
    ContinuousOn F (Ici (0 : ℝ)) := by
  intro x hx
  change 0 ≤ x at hx
  rcases eq_or_lt_of_le hx with hzero | hpositive_x
  · subst x
    exact continuousWithinAt_Ioi_iff_Ici.mp horigin
  · have hAt : ContinuousAt F x :=
      hpositive.continuousAt (isOpen_Ioi.mem_nhds hpositive_x)
    exact hAt.continuousWithinAt
