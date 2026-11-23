-- Prove2me | solution 1 for Csg.rpsSteps_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:53:22.053809+00:00
-- url     : https://prove2.me/submissions/00dd1318-3b9d-4684-b3ba-ab270f409d2c

import Definitions.Def_Csg_RockPaperScissors
import Definitions.Def_Csg_RewardUntilCertificate
import Definitions.Def_Csg_RockPaperScissorsSteps
import Theorems.Thm_Csg_rpsCSGSteps_stageValue_draw
import Theorems.Thm_Csg_rpsCSGSteps_stageValue_initial
import Theorems.Thm_Csg_CSG_bwInd_zero
import Theorems.Thm_Csg_CSG_reachBounded_zero
attribute [local simp] Csg.CSG.bwInd_zero
attribute [local simp] Csg.CSG.reachBounded_zero



set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution {w : RPSState → ℝ} (hw : rpsStepsStep w = w) : w = rpsSteps := by
  have hwin1 : w RPSState.win1 = 0 := by
    have h := congrFun hw RPSState.win1
    change (0 : ℝ) = w RPSState.win1 at h
    exact h.symm
  have hwin2 : w RPSState.win2 = 0 := by
    have h := congrFun hw RPSState.win2
    change (0 : ℝ) = w RPSState.win2 at h
    exact h.symm
  have hdraw : rpsCSGSteps.stageValue RPSState.draw w = w RPSState.draw := by
    have h := congrFun hw RPSState.draw
    change rpsCSGSteps.stageValue RPSState.draw w = w RPSState.draw at h
    exact h
  have hinit : rpsCSGSteps.stageValue RPSState.initial w = w RPSState.initial := by
    have h := congrFun hw RPSState.initial
    change rpsCSGSteps.stageValue RPSState.initial w = w RPSState.initial at h
    exact h
  rw [rpsCSGSteps_stageValue_draw] at hdraw
  rw [rpsCSGSteps_stageValue_initial, hwin1, hwin2] at hinit
  have hw_init : w RPSState.initial = 2 := by linarith
  have hw_draw : w RPSState.draw = 3 := by linarith
  funext s
  cases s with
  | win1 => simp [hwin1, rpsSteps]
  | win2 => simp [hwin2, rpsSteps]
  | initial => simp [hw_init, rpsSteps]
  | draw => simp [hw_draw, rpsSteps]
end Csg
