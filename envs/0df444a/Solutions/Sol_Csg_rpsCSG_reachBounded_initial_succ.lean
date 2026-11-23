-- Prove2me | solution 1 for Csg.rpsCSG_reachBounded_initial_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:32:33.618662+00:00
-- url     : https://prove2.me/submissions/d95b3f93-d5ea-40bb-9fbe-71ba85cac920

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors
import Theorems.Thm_Csg_rpsCSG_stageValue_initial
import Theorems.Thm_Csg_rpsCSG_reachBounded_win2
import Theorems.Thm_Csg_CSG_reachBounded_succ


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (k : ℕ) :
    rpsCSG.reachBounded rpsGoalWin2 (k + 1) .initial =
      (rpsCSG.reachBounded rpsGoalWin2 k .win1 + 1 +
        rpsCSG.reachBounded rpsGoalWin2 k .draw) / 3 := by
  rw [CSG.reachBounded_succ, if_neg (show ¬ rpsGoalWin2 .initial by decide),
    rpsCSG_stageValue_initial, rpsCSG_reachBounded_win2]
end Csg
