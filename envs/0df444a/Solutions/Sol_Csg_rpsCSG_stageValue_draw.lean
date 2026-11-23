-- Prove2me | solution 1 for Csg.rpsCSG_stageValue_draw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:25:54.414278+00:00
-- url     : https://prove2.me/submissions/4fc98c3d-3291-494d-8f47-b8209e2d3405

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors
import Theorems.Thm_Csg_MatrixGame_value_eq_of_forall_eq
import Theorems.Thm_Csg_rpsCSG_expect_draw
import Theorems.Thm_Csg_CSG_bwInd_zero
import Theorems.Thm_Csg_CSG_reachBounded_zero
attribute [local simp] Csg.CSG.bwInd_zero
attribute [local simp] Csg.CSG.reachBounded_zero



set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (v : RPSState → ℝ) : rpsCSG.stageValue .draw v = v .initial := by
  have hA : ∀ a1 a2, (rpsCSG.stageGame .draw v).A a1 a2 = v .initial := by
    intro a1 a2
    change rpsCSG.r .draw a1 a2 + rpsCSG.expect .draw a1 a2 v = v .initial
    rw [rpsCSG_expect_draw]
    simp [rpsCSG, rpsR]
  exact (rpsCSG.stageGame .draw v).value_eq_of_forall_eq hA
end Csg
