-- Prove2me | solution 1 for Csg.rpsVStar_le_of_prefixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:47:02.030068+00:00
-- url     : https://prove2.me/submissions/dda3f6b0-ee2f-49bb-bcdf-d335299cdee0

import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_RockPaperScissors
import Definitions.Def_Csg_RockPaperScissorsLfp
import Theorems.Thm_Csg_CSG_bwInd_zero
import Theorems.Thm_Csg_CSG_reachBounded_zero
import Theorems.Thm_Csg_rpsCSG_stageValue_draw
import Theorems.Thm_Csg_rpsCSG_stageValue_initial
attribute [local simp] Csg.CSG.bwInd_zero
attribute [local simp] Csg.CSG.reachBounded_zero



set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution {b : RPSState → Set.Icc (0 : ℝ) 1}
    (hb : rpsCSG.reachOp rpsGoalWin2 rpsR_zero b ≤ b) : rpsVStar ≤ b := by
  have hwin1 : (0 : ℝ) ≤ (b RPSState.win1 : ℝ) := (b RPSState.win1).2.1
  have hwin2 : (b RPSState.win2 : ℝ) = 1 := by
    have hle : (1 : ℝ) ≤ (b RPSState.win2 : ℝ) := hb RPSState.win2
    exact le_antisymm (b RPSState.win2).2.2 hle
  have hdraw_ge : (b RPSState.initial : ℝ) ≤ (b RPSState.draw : ℝ) := by
    have hle : rpsCSG.stageValue RPSState.draw (fun s' => (b s' : ℝ)) ≤
        (b RPSState.draw : ℝ) := hb RPSState.draw
    rwa [rpsCSG_stageValue_draw] at hle
  have hinit_ge : ((b RPSState.win1 : ℝ) + 1 + (b RPSState.draw : ℝ)) / 3 ≤
      (b RPSState.initial : ℝ) := by
    have hle : rpsCSG.stageValue RPSState.initial (fun s' => (b s' : ℝ)) ≤
        (b RPSState.initial : ℝ) := hb RPSState.initial
    rw [rpsCSG_stageValue_initial, hwin2] at hle
    linarith
  have hinit_half : (1 : ℝ) / 2 ≤ (b RPSState.initial : ℝ) := by linarith
  intro s
  cases s with
  | win1 => exact hwin1
  | win2 => exact hwin2.ge
  | initial =>
      change (rpsVStar RPSState.initial : ℝ) ≤ (b RPSState.initial : ℝ)
      simp only [rpsVStar]
      linarith
  | draw =>
      change (rpsVStar RPSState.draw : ℝ) ≤ (b RPSState.draw : ℝ)
      simp only [rpsVStar]
      linarith
end Csg
