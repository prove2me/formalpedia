-- Prove2me | solution 1 for Csg.rpsCSGSteps_expect_initial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:48:41.443213+00:00
-- url     : https://prove2.me/submissions/05620af5-515c-40e6-807f-212a43eb4b19

import Definitions.Def_Csg_RockPaperScissors
import Definitions.Def_Csg_RewardUntilCertificate
import Definitions.Def_Csg_RockPaperScissorsSteps
import Theorems.Thm_Csg_CSG_bwInd_zero
import Theorems.Thm_Csg_CSG_reachBounded_zero
attribute [local simp] Csg.CSG.bwInd_zero
attribute [local simp] Csg.CSG.reachBounded_zero



set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (a1 a2 : RPSAction) (v : RPSState → ℝ) :
    rpsCSGSteps.expect .initial a1 a2 v = v (outcome a1 a2) := by
  change ∑ s' : RPSState, (rpsK .initial a1 a2 s').toReal * v s' = v (outcome a1 a2)
  simp [rpsK, PMF.pure_apply, apply_ite ENNReal.toReal]
end Csg
