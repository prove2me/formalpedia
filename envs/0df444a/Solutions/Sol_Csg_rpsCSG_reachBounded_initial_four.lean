-- Prove2me | solution 1 for Csg.rpsCSG_reachBounded_initial_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:31:06.059941+00:00
-- url     : https://prove2.me/submissions/2094bc16-88c2-4880-adb5-3176c60ca25f

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors
import Theorems.Thm_P2M_Csg_rpsCSG_reachBounded_initial_succ__f2e1863eab60
import Theorems.Thm_Csg_rpsCSG_reachBounded_draw_three

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    rpsCSG.reachBounded rpsGoalWin2 4 .initial = 4 / 9 := by
  rw [rpsCSG_reachBounded_initial_succ', rpsCSG_reachBounded_draw_three]
  norm_num
end Csg
