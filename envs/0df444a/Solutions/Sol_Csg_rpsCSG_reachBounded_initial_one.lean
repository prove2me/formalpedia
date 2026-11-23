-- Prove2me | solution 1 for Csg.rpsCSG_reachBounded_initial_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:39:25.257485+00:00
-- url     : https://prove2.me/submissions/e0c28c73-2801-485c-ad36-c973808815b6

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors
import Theorems.Thm_P2M_Csg_rpsCSG_reachBounded_initial_succ__f2e1863eab60
import Theorems.Thm_Csg_rpsCSG_reachBounded_draw_zero

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution : rpsCSG.reachBounded rpsGoalWin2 1 .initial = 1 / 3 := by
  rw [rpsCSG_reachBounded_initial_succ', rpsCSG_reachBounded_draw_zero]
  norm_num
end Csg
