-- Prove2me | solution 1 for Csg.rpsLo_le_of_prefixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:51:08.791737+00:00
-- url     : https://prove2.me/submissions/2dc6af56-6741-4b09-9998-bcecf5a1e9ba

import Definitions.Def_Csg_IntervalCertificate
import Definitions.Def_Csg_RockPaperScissorsLfp
import Definitions.Def_Csg_RockPaperScissorsInterval
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
    (hb : rpsCSG.reachOp rpsGoalWin2 rpsR_zero b ≤ b) : rpsLo ≤ b := by
  have hwin1 : (0 : ℝ) ≤ (b RPSState.win1 : ℝ) := (b RPSState.win1).2.1
  have hwin2 : (1 : ℝ) ≤ (b RPSState.win2 : ℝ) := hb RPSState.win2
  have hdraw_nonneg : (0 : ℝ) ≤ (b RPSState.draw : ℝ) := (b RPSState.draw).2.1
  have hinit_ge : ((b RPSState.win1 : ℝ) + (b RPSState.win2 : ℝ) + (b RPSState.draw : ℝ)) / 3 ≤
      (b RPSState.initial : ℝ) := by
    have hle : rpsCSG.stageValue RPSState.initial (fun s' => (b s' : ℝ)) ≤
        (b RPSState.initial : ℝ) := hb RPSState.initial
    rwa [rpsCSG_stageValue_initial] at hle
  have hinit_third : (1 : ℝ) / 3 ≤ (b RPSState.initial : ℝ) := by linarith
  have hdraw_ge_init : (b RPSState.initial : ℝ) ≤ (b RPSState.draw : ℝ) := by
    have hle : rpsCSG.stageValue RPSState.draw (fun s' => (b s' : ℝ)) ≤
        (b RPSState.draw : ℝ) := hb RPSState.draw
    rwa [rpsCSG_stageValue_draw] at hle
  intro s
  cases s with
  | win1 => exact hwin1
  | win2 => exact hwin2
  | initial =>
      change (rpsLo RPSState.initial : ℝ) ≤ (b RPSState.initial : ℝ)
      simp only [rpsLo]
      linarith
  | draw =>
      change (rpsLo RPSState.draw : ℝ) ≤ (b RPSState.draw : ℝ)
      simp only [rpsLo]
      linarith
end Csg
