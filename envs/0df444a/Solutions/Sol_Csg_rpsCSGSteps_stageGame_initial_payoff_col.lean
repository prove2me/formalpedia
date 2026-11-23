-- Prove2me | solution 1 for Csg.rpsCSGSteps_stageGame_initial_payoff_col
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:50:54.3726+00:00
-- url     : https://prove2.me/submissions/7742e51f-9f77-423a-a5fa-82f1f6e9b415

import Definitions.Def_Csg_RockPaperScissors
import Definitions.Def_Csg_RewardUntilCertificate
import Definitions.Def_Csg_RockPaperScissorsSteps
import Theorems.Thm_Csg_rpsCSGSteps_stageGame_initial_A
import Theorems.Thm_Csg_CSG_bwInd_zero
import Theorems.Thm_Csg_CSG_reachBounded_zero
import Theorems.Thm_Csg_outcome_col_sum
import Theorems.Thm_Csg_rpsAction_sum
attribute [local simp] Csg.CSG.bwInd_zero
attribute [local simp] Csg.CSG.reachBounded_zero



set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (v : RPSState → ℝ) {q' : RPSAction → ℝ}
    (hq' : q' ∈ stdSimplex ℝ RPSAction) :
    (rpsCSGSteps.stageGame .initial v).payoff unif3 q' =
      1 + (v .win1 + v .win2 + v .draw) / 3 := by
  have hinner : ∀ a2, ∑ a1, unif3 a1 * (rpsCSGSteps.stageGame .initial v).A a1 a2 =
      1 + (v .win1 + v .win2 + v .draw) / 3 := by
    intro a2
    have hsum := outcome_col_sum a2 v
    rw [rpsAction_sum]
    simp only [rpsCSGSteps_stageGame_initial_A, unif3]
    linarith [hsum]
  rw [MatrixGame.payoff_eq_sum_mul']
  calc ∑ a2, (∑ a1, unif3 a1 * (rpsCSGSteps.stageGame .initial v).A a1 a2) * q' a2
      = ∑ a2, (1 + (v .win1 + v .win2 + v .draw) / 3) * q' a2 :=
        Finset.sum_congr rfl fun a2 _ => by rw [hinner a2]
    _ = (1 + (v .win1 + v .win2 + v .draw) / 3) * ∑ a2, q' a2 := by rw [← Finset.mul_sum]
    _ = 1 + (v .win1 + v .win2 + v .draw) / 3 := by rw [hq'.2, mul_one]
end Csg
