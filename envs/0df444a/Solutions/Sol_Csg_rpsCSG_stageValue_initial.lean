-- Prove2me | solution 1 for Csg.rpsCSG_stageValue_initial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:29:49.617356+00:00
-- url     : https://prove2.me/submissions/02f6acca-fc4a-467f-9bb4-0250ede8f0b9

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors
import Theorems.Thm_Csg_unif3_mem
import Theorems.Thm_Csg_rpsCSG_stageGame_initial_payoff_row
import Theorems.Thm_Csg_rpsCSG_stageGame_initial_payoff_col
import Theorems.Thm_Csg_MatrixGame_value_unique


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (v : RPSState → ℝ) :
    rpsCSG.stageValue .initial v = (v .win1 + v .win2 + v .draw) / 3 := by
  have huu : (rpsCSG.stageGame .initial v).payoff unif3 unif3 =
      (v .win1 + v .win2 + v .draw) / 3 := rpsCSG_stageGame_initial_payoff_row v unif3_mem
  have hrow : ∀ p' ∈ stdSimplex ℝ RPSAction,
      (rpsCSG.stageGame .initial v).payoff unif3 unif3 ≤
        (rpsCSG.stageGame .initial v).payoff p' unif3 := fun p' hp' =>
    le_of_eq (huu.trans (rpsCSG_stageGame_initial_payoff_row v hp').symm)
  have hcol : ∀ q' ∈ stdSimplex ℝ RPSAction,
      (rpsCSG.stageGame .initial v).payoff unif3 q' ≤
        (rpsCSG.stageGame .initial v).payoff unif3 unif3 := fun q' hq' =>
    le_of_eq ((rpsCSG_stageGame_initial_payoff_col v hq').trans huu.symm)
  have hval := (rpsCSG.stageGame .initial v).value_unique unif3_mem unif3_mem hrow hcol
  change (rpsCSG.stageGame .initial v).value = (v .win1 + v .win2 + v .draw) / 3
  rw [← hval]
  exact huu
end Csg
