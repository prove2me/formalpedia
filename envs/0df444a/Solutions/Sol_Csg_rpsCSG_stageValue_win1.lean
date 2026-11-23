-- Prove2me | solution 1 for Csg.rpsCSG_stageValue_win1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:25:43.725508+00:00
-- url     : https://prove2.me/submissions/7018a1e6-6b3c-4f74-8b3e-ea8104001993

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors
import Theorems.Thm_Csg_MatrixGame_value_eq_of_forall_eq
import Theorems.Thm_Csg_rpsCSG_expect_win1
import Theorems.Thm_Csg_CSG_bwInd_zero
import Theorems.Thm_Csg_CSG_reachBounded_zero
attribute [local simp] Csg.CSG.bwInd_zero
attribute [local simp] Csg.CSG.reachBounded_zero



set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (v : RPSState → ℝ) : rpsCSG.stageValue .win1 v = v .win1 := by
  have hA : ∀ a1 a2, (rpsCSG.stageGame .win1 v).A a1 a2 = v .win1 := by
    intro a1 a2
    change rpsCSG.r .win1 a1 a2 + rpsCSG.expect .win1 a1 a2 v = v .win1
    rw [rpsCSG_expect_win1]
    simp [rpsCSG, rpsR]
  exact (rpsCSG.stageGame .win1 v).value_eq_of_forall_eq hA
end Csg
