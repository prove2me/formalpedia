-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_sided_mesh_increment_to_jump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:17:47.148902+00:00
-- url     : https://prove2.me/submissions/726e971e-7d17-431a-8b5c-3cb91b2597d5

import Mathlib
-- The previous static import proposal omitted real and NNReal notation.
-- Preserve this pinned target's complete import preamble for the repair.

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set Topology
open scoped NNReal

/-- Sided mesh increments converge to the true left/right jump mark of a càdlàg path. -/
theorem solution
    (Y : ℝ≥0 → ℝ) (u : ℝ≥0)
    (hL : Tendsto Y (nhdsWithin u (Iio u))
      (𝓝 (Function.leftLim Y u)))
    (hR : ContinuousWithinAt Y (Ici u) u)
    (l r : ℕ → ℝ≥0)
    (hl : Tendsto l atTop (nhdsWithin u (Iio u)))
    (hr : Tendsto r atTop (nhdsWithin u (Ici u))) :
    Tendsto (fun n => Y (r n) - Y (l n))
      atTop (𝓝 (Y u - Function.leftLim Y u)) := by
  exact (hR.tendsto.comp hr).sub (hL.comp hl)
