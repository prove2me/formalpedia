-- Prove2me | solution 1 for Csg.rpsCSG_reachBounded_draw_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:42:47.250101+00:00
-- url     : https://prove2.me/submissions/71a821dd-2d69-4f99-8afb-957d52de057b

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors
import Theorems.Thm_Csg_rpsCSG_reachBounded_draw_succ
import Theorems.Thm_Csg_rpsCSG_reachBounded_initial_two

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution : rpsCSG.reachBounded rpsGoalWin2 3 .draw = 1 / 3 := by
  rw [rpsCSG_reachBounded_draw_succ, rpsCSG_reachBounded_initial_two]
end Csg
