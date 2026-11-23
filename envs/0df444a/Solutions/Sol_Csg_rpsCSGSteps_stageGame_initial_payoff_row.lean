-- Prove2me | solution 1 for Csg.rpsCSGSteps_stageGame_initial_payoff_row
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:50:33.294189+00:00
-- url     : https://prove2.me/submissions/1ed96f3e-f6f9-4035-bdc4-7eea447fe7c9

import Definitions.Def_Csg_RockPaperScissors
import Definitions.Def_Csg_RewardUntilCertificate
import Definitions.Def_Csg_RockPaperScissorsSteps
import Theorems.Thm_Csg_rpsCSGSteps_stageGame_initial_A
import Theorems.Thm_Csg_CSG_bwInd_zero
import Theorems.Thm_Csg_CSG_reachBounded_zero
import Theorems.Thm_Csg_outcome_row_sum
import Theorems.Thm_Csg_rpsAction_sum
attribute [local simp] Csg.CSG.bwInd_zero
attribute [local simp] Csg.CSG.reachBounded_zero



set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (v : RPSState → ℝ) {p' : RPSAction → ℝ}
    (hp' : p' ∈ stdSimplex ℝ RPSAction) :
    (rpsCSGSteps.stageGame .initial v).payoff p' unif3 =
      1 + (v .win1 + v .win2 + v .draw) / 3 := by
  have hinner : ∀ a1, ∑ a2, (rpsCSGSteps.stageGame .initial v).A a1 a2 * unif3 a2 =
      1 + (v .win1 + v .win2 + v .draw) / 3 := by
    intro a1
    have hsum := outcome_row_sum a1 v
    rw [rpsAction_sum]
    simp only [rpsCSGSteps_stageGame_initial_A, unif3]
    linarith [hsum]
  rw [MatrixGame.payoff_eq_sum_mul]
  calc ∑ a1, p' a1 * ∑ a2, (rpsCSGSteps.stageGame .initial v).A a1 a2 * unif3 a2
      = ∑ a1, p' a1 * (1 + (v .win1 + v .win2 + v .draw) / 3) :=
        Finset.sum_congr rfl fun a1 _ => by rw [hinner a1]
    _ = (∑ a1, p' a1) * (1 + (v .win1 + v .win2 + v .draw) / 3) := by rw [← Finset.sum_mul]
    _ = 1 + (v .win1 + v .win2 + v .draw) / 3 := by rw [hp'.2, one_mul]
end Csg
