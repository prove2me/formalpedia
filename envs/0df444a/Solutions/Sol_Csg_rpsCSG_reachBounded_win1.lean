-- Prove2me | solution 1 for Csg.rpsCSG_reachBounded_win1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:26:31.713276+00:00
-- url     : https://prove2.me/submissions/624a8a86-fcd7-40e3-a315-656de6e6e706

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors
import Theorems.Thm_Csg_rpsCSG_stageValue_win1
import Theorems.Thm_Csg_CSG_bwInd_zero
import Theorems.Thm_Csg_CSG_reachBounded_succ
import Theorems.Thm_Csg_CSG_reachBounded_zero
attribute [local simp] Csg.CSG.bwInd_zero
attribute [local simp] Csg.CSG.reachBounded_zero



set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (k : ℕ) : rpsCSG.reachBounded rpsGoalWin2 k .win1 = 0 := by
  induction k with
  | zero => simp [CSG.reachBounded_zero, rpsGoalWin2]
  | succ k ih =>
      rw [CSG.reachBounded_succ, if_neg (show ¬ rpsGoalWin2 .win1 by decide),
        rpsCSG_stageValue_win1, ih]
end Csg
