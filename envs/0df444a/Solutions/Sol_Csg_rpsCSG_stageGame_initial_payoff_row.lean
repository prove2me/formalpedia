-- Prove2me | solution 1 for Csg.rpsCSG_stageGame_initial_payoff_row
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:26:59.660837+00:00
-- url     : https://prove2.me/submissions/ac8fe592-b6f0-41cd-b0fe-0a39f4252ddc

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors
import Theorems.Thm_Csg_rpsAction_sum
import Theorems.Thm_Csg_outcome_row_sum
import Theorems.Thm_Csg_rpsCSG_stageGame_initial_A
import Theorems.Thm_Csg_CSG_bwInd_zero
import Theorems.Thm_Csg_CSG_reachBounded_zero
attribute [local simp] Csg.CSG.bwInd_zero
attribute [local simp] Csg.CSG.reachBounded_zero



set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (v : RPSState → ℝ) {p' : RPSAction → ℝ}
    (hp' : p' ∈ stdSimplex ℝ RPSAction) :
    (rpsCSG.stageGame .initial v).payoff p' unif3 = (v .win1 + v .win2 + v .draw) / 3 := by
  have hinner : ∀ a1, ∑ a2, (rpsCSG.stageGame .initial v).A a1 a2 * unif3 a2 =
      (v .win1 + v .win2 + v .draw) / 3 := by
    intro a1
    have hsum := outcome_row_sum a1 v
    rw [rpsAction_sum]
    simp only [rpsCSG_stageGame_initial_A, unif3]
    linarith [hsum]
  rw [MatrixGame.payoff_eq_sum_mul]
  calc ∑ a1, p' a1 * ∑ a2, (rpsCSG.stageGame .initial v).A a1 a2 * unif3 a2
      = ∑ a1, p' a1 * ((v .win1 + v .win2 + v .draw) / 3) :=
        Finset.sum_congr rfl fun a1 _ => by rw [hinner a1]
    _ = (∑ a1, p' a1) * ((v .win1 + v .win2 + v .draw) / 3) := by rw [← Finset.sum_mul]
    _ = (v .win1 + v .win2 + v .draw) / 3 := by rw [hp'.2, one_mul]
end Csg
