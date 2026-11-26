-- Prove2me | solution 1 for FriedCrossing.TwinRate.wPlus_sub_wMinus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:54:56.486827+00:00
-- url     : https://prove2.me/submissions/335fafcb-d9b1-4df5-aa4b-2394567d9970

import Definitions.Def_B1s_fried_crossing_9_03
import Definitions.Def_B1s_fried_crossing_rate_9_07

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.TwinRate
namespace FriedCrossing.TwinRate
theorem _root_.solution (a b : ℝ) : wPlus a b - wMinus a b = Real.sqrt (disc a b) := by
  unfold wPlus wMinus; ring
end FriedCrossing.TwinRate
