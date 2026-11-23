-- Prove2me | solution 1 for Csg.rpsVStarSafety_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:49:05.125592+00:00
-- url     : https://prove2.me/submissions/c02e5a39-1303-4568-8355-b53cbe70416b

import Definitions.Def_Csg_SafetyCertificate
import Definitions.Def_Csg_RockPaperScissorsLfp
import Definitions.Def_Csg_RockPaperScissorsSafety
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
    (hb : b ≤ rpsCSG.safetyOp rpsSafeUnresolved rpsR_zero b) : b ≤ rpsVStarSafety := by
  have hwin1_le : (b RPSState.win1 : ℝ) ≤ 0 := hb RPSState.win1
  have hwin2_le : (b RPSState.win2 : ℝ) ≤ 0 := hb RPSState.win2
  have hwin1_eq : (b RPSState.win1 : ℝ) = 0 := le_antisymm hwin1_le (b RPSState.win1).2.1
  have hwin2_eq : (b RPSState.win2 : ℝ) = 0 := le_antisymm hwin2_le (b RPSState.win2).2.1
  have hdraw_le : (b RPSState.draw : ℝ) ≤ (b RPSState.initial : ℝ) := by
    have hle : (b RPSState.draw : ℝ) ≤
        rpsCSG.stageValue RPSState.draw (fun s' => (b s' : ℝ)) := hb RPSState.draw
    rwa [rpsCSG_stageValue_draw] at hle
  have hinit_le : (b RPSState.initial : ℝ) ≤
      ((b RPSState.win1 : ℝ) + (b RPSState.win2 : ℝ) + (b RPSState.draw : ℝ)) / 3 := by
    have hle : (b RPSState.initial : ℝ) ≤
        rpsCSG.stageValue RPSState.initial (fun s' => (b s' : ℝ)) := hb RPSState.initial
    rwa [rpsCSG_stageValue_initial] at hle
  have hdraw_eq : (b RPSState.draw : ℝ) = 0 := by
    have hb_draw_nonneg : (0 : ℝ) ≤ (b RPSState.draw : ℝ) := (b RPSState.draw).2.1
    rw [hwin1_eq, hwin2_eq] at hinit_le
    linarith
  intro s
  cases s with
  | win1 => exact hwin1_eq.le
  | win2 => exact hwin2_eq.le
  | draw =>
      change (b RPSState.draw : ℝ) ≤ (rpsVStarSafety RPSState.draw : ℝ)
      simp only [rpsVStarSafety]
      linarith
  | initial =>
      change (b RPSState.initial : ℝ) ≤ (rpsVStarSafety RPSState.initial : ℝ)
      simp only [rpsVStarSafety]
      linarith
end Csg
