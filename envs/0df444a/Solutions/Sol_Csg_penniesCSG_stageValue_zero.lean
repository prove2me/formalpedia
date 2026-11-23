-- Prove2me | solution 1 for Csg.penniesCSG_stageValue_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:30:17.222158+00:00
-- url     : https://prove2.me/submissions/dc403b83-d494-4047-a378-b1a1f2921763

import Definitions.Def_Csg_BackwardInduction
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_MatchingPennies
import Theorems.Thm_Csg_unif2_mem
import Theorems.Thm_Csg_penniesMatrix_payoff_row
import Theorems.Thm_Csg_penniesMatrix_payoff_col
import Theorems.Thm_Csg_penniesCSG_stageGame_zero_payoff
import Theorems.Thm_Csg_MatrixGame_value_unique


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution : penniesCSG.stageValue () (0 : Unit → ℝ) = 0 := by
  change (penniesCSG.stageGame () (0 : Unit → ℝ)).value = 0
  have huu : (penniesCSG.stageGame () (0 : Unit → ℝ)).payoff unif2 unif2 = 0 := by
    rw [penniesCSG_stageGame_zero_payoff]
    exact penniesMatrix_payoff_row unif2
  have hrow : ∀ p' ∈ stdSimplex ℝ (Fin 2),
      (penniesCSG.stageGame () (0 : Unit → ℝ)).payoff unif2 unif2 ≤
        (penniesCSG.stageGame () (0 : Unit → ℝ)).payoff p' unif2 := by
    intro p' _
    rw [huu, penniesCSG_stageGame_zero_payoff]
    exact (penniesMatrix_payoff_row p').ge
  have hcol : ∀ q' ∈ stdSimplex ℝ (Fin 2),
      (penniesCSG.stageGame () (0 : Unit → ℝ)).payoff unif2 q' ≤
        (penniesCSG.stageGame () (0 : Unit → ℝ)).payoff unif2 unif2 := by
    intro q' _
    rw [huu, penniesCSG_stageGame_zero_payoff]
    exact (penniesMatrix_payoff_col q').le
  have hval := (penniesCSG.stageGame () (0 : Unit → ℝ)).value_unique unif2_mem unif2_mem hrow hcol
  rw [← hval]
  exact huu
end Csg
