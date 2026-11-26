-- Prove2me | solution 1 for FriedCrossing.TwinRate.continuousAt_wPlus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:39:42.248275+00:00
-- url     : https://prove2.me/submissions/c2937c2a-b245-42a0-833f-a669ee70aeab

import Definitions.Def_B1s_fried_crossing_9_03
import Definitions.Def_B1s_fried_crossing_rate_9_07

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.TwinRate
namespace FriedCrossing.TwinRate
theorem _root_.solution (p : ℝ × ℝ) :
    ContinuousAt (fun q : ℝ × ℝ => wPlus q.1 q.2) p := by
  unfold wPlus disc
  fun_prop
end FriedCrossing.TwinRate
