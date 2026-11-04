-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_shrinking_cell_increment_converges_to_actual_jump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:35:40.617366+00:00
-- url     : https://prove2.me/submissions/4d860713-39ba-4e2c-bac0-7ae414807a4e

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology
open scoped NNReal

/-- The limiting increment along any genuine straddling shrinkage is the
intrinsic cadlag jump of the same path. -/
theorem solution (Y : ℝ≥0 → ℝ) (u : ℝ≥0) (a b : ℕ → ℝ≥0)
    (ha : Tendsto a atTop (𝓝[<] u))
    (hb : Tendsto b atTop (nhdsWithin u (Ici u)))
    (hL : Tendsto Y (𝓝[<] u) (𝓝 (Function.leftLim Y u)))
    (hR : ContinuousWithinAt Y (Ici u) u) :
    Tendsto (fun n => Y (b n) - Y (a n)) atTop
      (𝓝 (Y u - Function.leftLim Y u)) := by
  exact (hR.tendsto.comp hb).sub (hL.comp ha)
