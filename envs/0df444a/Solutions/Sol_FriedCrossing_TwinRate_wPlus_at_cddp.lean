-- Prove2me | solution 1 for FriedCrossing.TwinRate.wPlus_at_cddp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:39:20.514122+00:00
-- url     : https://prove2.me/submissions/d658bff7-14b7-4d58-88b3-8fbf85b2b035

import Definitions.Def_B1s_fried_crossing_9_03
import Definitions.Def_B1s_fried_crossing_rate_9_07

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.TwinRate
namespace FriedCrossing.TwinRate
theorem _root_.solution {r₀ : ℝ} (hr₀ : 0 < r₀) : wPlus r₀ 0 = r₀ := by
  unfold wPlus disc
  rw [mul_zero, sub_zero, Real.sqrt_sq hr₀.le]; ring
end FriedCrossing.TwinRate
