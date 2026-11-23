-- Prove2me | solution 1 for Csg.rpsCSG_stageGame_initial_payoff_col
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:27:05.834026+00:00
-- url     : https://prove2.me/submissions/1c110f12-ce73-426f-9180-5b96b409f087

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors
import Theorems.Thm_Csg_rpsAction_sum
import Theorems.Thm_Csg_outcome_col_sum
import Theorems.Thm_Csg_rpsCSG_stageGame_initial_A
import Theorems.Thm_Csg_CSG_bwInd_zero
import Theorems.Thm_Csg_CSG_reachBounded_zero
attribute [local simp] Csg.CSG.bwInd_zero
attribute [local simp] Csg.CSG.reachBounded_zero



set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (v : RPSState → ℝ) {q' : RPSAction → ℝ}
    (hq' : q' ∈ stdSimplex ℝ RPSAction) :
    (rpsCSG.stageGame .initial v).payoff unif3 q' = (v .win1 + v .win2 + v .draw) / 3 := by
  have hinner : ∀ a2, ∑ a1, unif3 a1 * (rpsCSG.stageGame .initial v).A a1 a2 =
      (v .win1 + v .win2 + v .draw) / 3 := by
    intro a2
    have hsum := outcome_col_sum a2 v
    rw [rpsAction_sum]
    simp only [rpsCSG_stageGame_initial_A, unif3]
    linarith [hsum]
  rw [MatrixGame.payoff_eq_sum_mul']
  calc ∑ a2, (∑ a1, unif3 a1 * (rpsCSG.stageGame .initial v).A a1 a2) * q' a2
      = ∑ a2, ((v .win1 + v .win2 + v .draw) / 3) * q' a2 :=
        Finset.sum_congr rfl fun a2 _ => by rw [hinner a2]
    _ = ((v .win1 + v .win2 + v .draw) / 3) * ∑ a2, q' a2 := by rw [← Finset.mul_sum]
    _ = (v .win1 + v .win2 + v .draw) / 3 := by rw [hq'.2, mul_one]
end Csg
