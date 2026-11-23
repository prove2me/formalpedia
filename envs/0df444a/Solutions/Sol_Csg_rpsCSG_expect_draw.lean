-- Prove2me | solution 1 for Csg.rpsCSG_expect_draw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:25:07.597335+00:00
-- url     : https://prove2.me/submissions/45dd5cd8-92e7-46e8-9f64-ce6b9a0e7463

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
    rpsCSG.expect .draw a1 a2 v = v .initial := by
  change ∑ s' : RPSState, (rpsK .draw a1 a2 s').toReal * v s' = v .initial
  simp [rpsK, PMF.pure_apply, apply_ite ENNReal.toReal]
end Csg
