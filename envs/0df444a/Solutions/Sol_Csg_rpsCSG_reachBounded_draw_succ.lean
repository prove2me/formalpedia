-- Prove2me | solution 1 for Csg.rpsCSG_reachBounded_draw_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:27:03.227464+00:00
-- url     : https://prove2.me/submissions/991abaf6-1a70-43ae-8c8e-f90964f08242

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors
import Theorems.Thm_Csg_rpsCSG_stageValue_draw
import Theorems.Thm_Csg_CSG_reachBounded_succ


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (k : ℕ) :
    rpsCSG.reachBounded rpsGoalWin2 (k + 1) .draw = rpsCSG.reachBounded rpsGoalWin2 k .initial := by
  rw [CSG.reachBounded_succ, if_neg (show ¬ rpsGoalWin2 .draw by decide),
    rpsCSG_stageValue_draw]
end Csg
