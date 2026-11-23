-- Prove2me | solution 1 for Csg.rpsCSG_expect_initial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:25:15.276805+00:00
-- url     : https://prove2.me/submissions/0b2d887a-a6f0-436b-a343-4d3090e08098

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors
import Theorems.Thm_Csg_CSG_bwInd_zero
import Theorems.Thm_Csg_CSG_reachBounded_zero
attribute [local simp] Csg.CSG.bwInd_zero
attribute [local simp] Csg.CSG.reachBounded_zero



set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (a1 a2 : RPSAction) (v : RPSState → ℝ) :
    rpsCSG.expect .initial a1 a2 v = v (outcome a1 a2) := by
  change ∑ s' : RPSState, (rpsK .initial a1 a2 s').toReal * v s' = v (outcome a1 a2)
  simp [rpsK, PMF.pure_apply, apply_ite ENNReal.toReal]
end Csg
