-- Prove2me | solution 1 for Csg.rpsVStar_fixed_until
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:47:45.234982+00:00
-- url     : https://prove2.me/submissions/dcebdfd7-d21f-4d80-ae64-d928f84ae98a

import Definitions.Def_Csg_UntilOp
import Definitions.Def_Csg_RockPaperScissorsLfp
import Definitions.Def_Csg_RockPaperScissorsUntil
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
    rpsCSG.untilOp rpsSafeNotWin1 rpsGoalWin2 rpsR_zero rpsVStar = rpsVStar := by
  funext s
  apply Subtype.ext
  cases s with
  | win1 => rfl
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
