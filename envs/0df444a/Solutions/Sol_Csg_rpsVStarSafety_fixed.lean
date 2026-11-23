-- Prove2me | solution 1 for Csg.rpsVStarSafety_fixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:49:04.357521+00:00
-- url     : https://prove2.me/submissions/82772d7e-6127-4d7a-b158-ecc407be4d9e

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
theorem _root_.solution :
    rpsCSG.safetyOp rpsSafeUnresolved rpsR_zero rpsVStarSafety = rpsVStarSafety := by
  funext s
  apply Subtype.ext
  cases s with
  | win1 => rfl
  | win2 => rfl
  | initial =>
      change rpsCSG.stageValue RPSState.initial (fun s' => (rpsVStarSafety s' : ℝ)) =
        (rpsVStarSafety RPSState.initial : ℝ)
      rw [rpsCSG_stageValue_initial]
      norm_num [rpsVStarSafety]
  | draw =>
      change rpsCSG.stageValue RPSState.draw (fun s' => (rpsVStarSafety s' : ℝ)) =
        (rpsVStarSafety RPSState.draw : ℝ)
      rw [rpsCSG_stageValue_draw]
      simp only [rpsVStarSafety]
end Csg
