-- Prove2me | solution 1 for Csg.rpsCSG_reachBounded_draw_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:29:25.263562+00:00
-- url     : https://prove2.me/submissions/de96cda3-8c0b-411c-be7a-ced95c944d4f

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors
import Theorems.Thm_Csg_rpsCSG_reachBounded_draw_succ
import Theorems.Thm_Csg_rpsCSG_reachBounded_initial_zero

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution : rpsCSG.reachBounded rpsGoalWin2 1 .draw = 0 := by
  rw [rpsCSG_reachBounded_draw_succ, rpsCSG_reachBounded_initial_zero]
end Csg
