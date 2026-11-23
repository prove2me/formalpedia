-- Prove2me | solution 1 for Csg.rpsCSG_stageGame_initial_A
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:25:50.554019+00:00
-- url     : https://prove2.me/submissions/648ad3d1-f0b6-48fe-9a92-d8b4f19875b9

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors
import Theorems.Thm_Csg_rpsCSG_expect_initial
import Theorems.Thm_Csg_CSG_bwInd_zero
import Theorems.Thm_Csg_CSG_reachBounded_zero
attribute [local simp] Csg.CSG.bwInd_zero
attribute [local simp] Csg.CSG.reachBounded_zero



set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (a1 a2 : RPSAction) (v : RPSState → ℝ) :
    (rpsCSG.stageGame .initial v).A a1 a2 = v (outcome a1 a2) := by
  change rpsCSG.r .initial a1 a2 + rpsCSG.expect .initial a1 a2 v = v (outcome a1 a2)
  rw [rpsCSG_expect_initial]
  simp [rpsCSG, rpsR]
end Csg
