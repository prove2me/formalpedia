-- Prove2me | solution 1 for Csg.outcome_row_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:14:09.103482+00:00
-- url     : https://prove2.me/submissions/dab4f2cf-d25d-4736-b61f-c7ad2d315a72

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
theorem _root_.solution (a1 : RPSAction) (v : RPSState → ℝ) :
    v (outcome a1 .rock) + v (outcome a1 .paper) + v (outcome a1 .scissors) =
      v .win1 + v .win2 + v .draw := by
  cases a1 <;> simp only [outcome] <;> ring
end Csg
