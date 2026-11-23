-- Prove2me | solution 1 for Csg.rpsCSGSteps_stageGame_initial_A
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:49:30.310162+00:00
-- url     : https://prove2.me/submissions/a84093b3-88f4-4630-8c86-4184e9a2327f

import Definitions.Def_Csg_RockPaperScissors
import Definitions.Def_Csg_RewardUntilCertificate
import Definitions.Def_Csg_RockPaperScissorsSteps
import Theorems.Thm_Csg_rpsCSGSteps_expect_initial
import Theorems.Thm_Csg_CSG_bwInd_zero
import Theorems.Thm_Csg_CSG_reachBounded_zero
attribute [local simp] Csg.CSG.bwInd_zero
attribute [local simp] Csg.CSG.reachBounded_zero



set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (a1 a2 : RPSAction) (v : RPSState → ℝ) :
    (rpsCSGSteps.stageGame .initial v).A a1 a2 = 1 + v (outcome a1 a2) := by
  change rpsCSGSteps.r .initial a1 a2 + rpsCSGSteps.expect .initial a1 a2 v =
    1 + v (outcome a1 a2)
  rw [rpsCSGSteps_expect_initial]
  simp [rpsCSGSteps]
end Csg
