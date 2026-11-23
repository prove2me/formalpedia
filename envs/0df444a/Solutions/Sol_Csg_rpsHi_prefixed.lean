-- Prove2me | solution 1 for Csg.rpsHi_prefixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:51:11.634799+00:00
-- url     : https://prove2.me/submissions/dae4287a-fcba-4018-94e3-44f3ed9ea8b0

import Definitions.Def_Csg_IntervalCertificate
import Definitions.Def_Csg_RockPaperScissorsLfp
import Definitions.Def_Csg_RockPaperScissorsInterval
import Theorems.Thm_Csg_rpsCSG_stageValue_draw
import Theorems.Thm_Csg_rpsCSG_stageValue_initial
import Theorems.Thm_Csg_rpsCSG_stageValue_win1


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution : rpsCSG.reachOp rpsGoalWin2 rpsR_zero rpsHi ≤ rpsHi := by
  intro s
  cases s with
  | win1 =>
      change (rpsCSG.stageValue RPSState.win1 (fun s' => (rpsHi s' : ℝ)) : ℝ) ≤
        (rpsHi RPSState.win1 : ℝ)
      rw [rpsCSG_stageValue_win1]
  | win2 => exact le_refl _
  | initial =>
      change (rpsCSG.stageValue RPSState.initial (fun s' => (rpsHi s' : ℝ)) : ℝ) ≤
        (rpsHi RPSState.initial : ℝ)
      rw [rpsCSG_stageValue_initial]
      norm_num [rpsHi]
  | draw =>
      change (rpsCSG.stageValue RPSState.draw (fun s' => (rpsHi s' : ℝ)) : ℝ) ≤
        (rpsHi RPSState.draw : ℝ)
      rw [rpsCSG_stageValue_draw]
      norm_num [rpsHi]
end Csg
