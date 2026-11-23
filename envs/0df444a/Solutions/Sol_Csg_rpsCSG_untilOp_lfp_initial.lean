-- Prove2me | solution 1 for Csg.rpsCSG_untilOp_lfp_initial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:41:25.786809+00:00
-- url     : https://prove2.me/submissions/76918460-86f9-4459-bf53-50c431e62de8

import Definitions.Def_Csg_UntilOp
import Definitions.Def_Csg_RockPaperScissorsLfp
import Definitions.Def_Csg_RockPaperScissorsUntil
import Theorems.Thm_Csg_rpsCSG_untilOp_lfp_eq
import Theorems.Thm_Csg_CSG_bwInd_zero
import Theorems.Thm_Csg_CSG_reachBounded_zero
attribute [local simp] Csg.CSG.bwInd_zero
attribute [local simp] Csg.CSG.reachBounded_zero



set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    ((rpsCSG.untilOp rpsSafeNotWin1 rpsGoalWin2 rpsR_zero).lfp RPSState.initial : ℝ) = 1 / 2 := by
  rw [rpsCSG_untilOp_lfp_eq]
  simp [rpsVStar]
end Csg
