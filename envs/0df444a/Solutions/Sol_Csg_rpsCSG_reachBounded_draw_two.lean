-- Prove2me | solution 1 for Csg.rpsCSG_reachBounded_draw_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:42:41.728438+00:00
-- url     : https://prove2.me/submissions/e7b3659f-2a5d-410c-835e-b512c304949c

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors
import Theorems.Thm_Csg_rpsCSG_reachBounded_draw_succ
import Theorems.Thm_Csg_rpsCSG_reachBounded_initial_one

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution : rpsCSG.reachBounded rpsGoalWin2 2 .draw = 1 / 3 := by
  rw [rpsCSG_reachBounded_draw_succ, rpsCSG_reachBounded_initial_one]
end Csg
