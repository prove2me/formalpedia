-- Prove2me | solution 1 for Csg.rpsCSG_reachBounded_win2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:25:17.244637+00:00
-- url     : https://prove2.me/submissions/4382c4de-b65c-41e1-9b6d-27ee57516de2

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors
import Theorems.Thm_Csg_CSG_reachBounded_of_goal


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (k : ℕ) : rpsCSG.reachBounded rpsGoalWin2 k .win2 = 1 :=
  rpsCSG.reachBounded_of_goal rpsGoalWin2 k rfl
end Csg
