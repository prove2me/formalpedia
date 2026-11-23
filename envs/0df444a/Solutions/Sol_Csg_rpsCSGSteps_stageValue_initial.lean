-- Prove2me | solution 1 for Csg.rpsCSGSteps_stageValue_initial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:51:42.785239+00:00
-- url     : https://prove2.me/submissions/a15c1223-ddd7-45b3-a588-b70adcfbd37f

import Definitions.Def_Csg_RockPaperScissors
import Definitions.Def_Csg_RewardUntilCertificate
import Definitions.Def_Csg_RockPaperScissorsSteps
import Theorems.Thm_Csg_rpsCSGSteps_stageGame_initial_payoff_row
import Theorems.Thm_Csg_rpsCSGSteps_stageGame_initial_payoff_col
import Theorems.Thm_Csg_MatrixGame_value_unique
import Theorems.Thm_Csg_unif3_mem


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (v : RPSState → ℝ) :
    rpsCSGSteps.stageValue .initial v = 1 + (v .win1 + v .win2 + v .draw) / 3 := by
  have huu : (rpsCSGSteps.stageGame .initial v).payoff unif3 unif3 =
      1 + (v .win1 + v .win2 + v .draw) / 3 := rpsCSGSteps_stageGame_initial_payoff_row v unif3_mem
  have hrow : ∀ p' ∈ stdSimplex ℝ RPSAction,
      (rpsCSGSteps.stageGame .initial v).payoff unif3 unif3 ≤
        (rpsCSGSteps.stageGame .initial v).payoff p' unif3 := fun p' hp' =>
    le_of_eq (huu.trans (rpsCSGSteps_stageGame_initial_payoff_row v hp').symm)
  have hcol : ∀ q' ∈ stdSimplex ℝ RPSAction,
      (rpsCSGSteps.stageGame .initial v).payoff unif3 q' ≤
        (rpsCSGSteps.stageGame .initial v).payoff unif3 unif3 := fun q' hq' =>
    le_of_eq ((rpsCSGSteps_stageGame_initial_payoff_col v hq').trans huu.symm)
  have hval := (rpsCSGSteps.stageGame .initial v).value_unique unif3_mem unif3_mem hrow hcol
  change (rpsCSGSteps.stageGame .initial v).value = 1 + (v .win1 + v .win2 + v .draw) / 3
  rw [← hval]
  exact huu
end Csg
