-- Prove2me | solution 1 for Csg.rpsCSGSteps_expect_draw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:48:34.597981+00:00
-- url     : https://prove2.me/submissions/363d19f5-76f5-494d-93ec-8a0ad6efc63a

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
    rpsCSGSteps.expect .draw a1 a2 v = v .initial := by
  change ∑ s' : RPSState, (rpsK .draw a1 a2 s').toReal * v s' = v .initial
  simp [rpsK, PMF.pure_apply, apply_ite ENNReal.toReal]
end Csg
