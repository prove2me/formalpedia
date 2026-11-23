-- Prove2me | solution 1 for Csg.rpsCSGSteps_stageValue_draw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:49:34.887279+00:00
-- url     : https://prove2.me/submissions/fd2be0c0-6031-4418-b9c2-a14084ba0d19

import Definitions.Def_Csg_RockPaperScissors
import Definitions.Def_Csg_RewardUntilCertificate
import Definitions.Def_Csg_RockPaperScissorsSteps
import Theorems.Thm_Csg_rpsCSGSteps_expect_draw
import Theorems.Thm_Csg_CSG_bwInd_zero
import Theorems.Thm_Csg_CSG_reachBounded_zero
import Theorems.Thm_Csg_MatrixGame_value_eq_of_forall_eq
attribute [local simp] Csg.CSG.bwInd_zero
attribute [local simp] Csg.CSG.reachBounded_zero



set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (v : RPSState → ℝ) :
    rpsCSGSteps.stageValue .draw v = 1 + v .initial := by
  have hA : ∀ a1 a2, (rpsCSGSteps.stageGame .draw v).A a1 a2 = 1 + v .initial := by
    intro a1 a2
    change rpsCSGSteps.r .draw a1 a2 + rpsCSGSteps.expect .draw a1 a2 v = 1 + v .initial
    rw [rpsCSGSteps_expect_draw]
    simp [rpsCSGSteps]
  exact (rpsCSGSteps.stageGame .draw v).value_eq_of_forall_eq hA
end Csg
