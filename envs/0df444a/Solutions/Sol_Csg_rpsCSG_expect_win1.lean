-- Prove2me | solution 1 for Csg.rpsCSG_expect_win1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:25:06.791941+00:00
-- url     : https://prove2.me/submissions/de0033c3-f548-4d11-adf4-d1202c00594b

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
    rpsCSG.expect .win1 a1 a2 v = v .win1 := by
  change ∑ s' : RPSState, (rpsK .win1 a1 a2 s').toReal * v s' = v .win1
  simp [rpsK, PMF.pure_apply, apply_ite ENNReal.toReal]
end Csg
