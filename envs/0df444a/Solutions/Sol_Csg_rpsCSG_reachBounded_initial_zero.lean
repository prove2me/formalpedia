-- Prove2me | solution 1 for Csg.rpsCSG_reachBounded_initial_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:25:25.132989+00:00
-- url     : https://prove2.me/submissions/7a641650-4261-44d0-a117-61d3c7c47332

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors
import Theorems.Thm_Csg_CSG_bwInd_zero
import Theorems.Thm_Csg_CSG_reachBounded_zero
attribute [local simp] Csg.CSG.bwInd_zero
attribute [local simp] Csg.CSG.reachBounded_zero



set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution : rpsCSG.reachBounded rpsGoalWin2 0 .initial = 0 := by
  simp [CSG.reachBounded_zero, rpsGoalWin2]
end Csg
