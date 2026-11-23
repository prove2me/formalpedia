-- Prove2me | solution 1 for Csg.rpsCSG_reachOp_lfp_initial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:40:41.473527+00:00
-- url     : https://prove2.me/submissions/8e027080-ab5b-456f-8739-6db7e7385bac

import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_RockPaperScissors
import Definitions.Def_Csg_RockPaperScissorsLfp
import Theorems.Thm_Csg_rpsCSG_reachOp_lfp_eq
import Theorems.Thm_Csg_CSG_bwInd_zero
import Theorems.Thm_Csg_CSG_reachBounded_zero
attribute [local simp] Csg.CSG.bwInd_zero
attribute [local simp] Csg.CSG.reachBounded_zero



set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    ((rpsCSG.reachOp rpsGoalWin2 rpsR_zero).lfp RPSState.initial : ℝ) = 1 / 2 := by
  rw [rpsCSG_reachOp_lfp_eq]
  simp [rpsVStar]
end Csg
