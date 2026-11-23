-- Prove2me | solution 1 for Csg.rpsCSG_reachBounded_initial_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:39:30.373234+00:00
-- url     : https://prove2.me/submissions/08dbaec0-c8fc-46f3-83d5-101be92d4413

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors
import Theorems.Thm_P2M_Csg_rpsCSG_reachBounded_initial_succ__f2e1863eab60
import Theorems.Thm_Csg_rpsCSG_reachBounded_draw_one

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution : rpsCSG.reachBounded rpsGoalWin2 2 .initial = 1 / 3 := by
  rw [rpsCSG_reachBounded_initial_succ', rpsCSG_reachBounded_draw_one]
  norm_num
end Csg
