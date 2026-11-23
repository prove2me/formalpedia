-- Prove2me | solution 1 for Csg.rpsVStar_fixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:46:57.464743+00:00
-- url     : https://prove2.me/submissions/b0c962d2-6d74-4954-949b-34c022c5d545

import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_RockPaperScissors
import Definitions.Def_Csg_RockPaperScissorsLfp
import Theorems.Thm_Csg_CSG_bwInd_zero
import Theorems.Thm_Csg_CSG_reachBounded_zero
import Theorems.Thm_Csg_rpsCSG_stageValue_draw
import Theorems.Thm_Csg_rpsCSG_stageValue_initial
import Theorems.Thm_Csg_rpsCSG_stageValue_win1
attribute [local simp] Csg.CSG.bwInd_zero
attribute [local simp] Csg.CSG.reachBounded_zero



set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    rpsCSG.reachOp rpsGoalWin2 rpsR_zero rpsVStar = rpsVStar := by
  funext s
  apply Subtype.ext
  cases s with
  | win1 =>
      change rpsCSG.stageValue RPSState.win1 (fun s' => (rpsVStar s' : ℝ)) =
        (rpsVStar RPSState.win1 : ℝ)
      rw [rpsCSG_stageValue_win1]
  | win2 => rfl
  | initial =>
      change rpsCSG.stageValue RPSState.initial (fun s' => (rpsVStar s' : ℝ)) =
        (rpsVStar RPSState.initial : ℝ)
      rw [rpsCSG_stageValue_initial]
      norm_num [rpsVStar]
  | draw =>
      change rpsCSG.stageValue RPSState.draw (fun s' => (rpsVStar s' : ℝ)) =
        (rpsVStar RPSState.draw : ℝ)
      rw [rpsCSG_stageValue_draw]
      simp only [rpsVStar]
end Csg
