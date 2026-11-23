-- Prove2me | solution 1 for Csg.penniesMatrix_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:30:30.788779+00:00
-- url     : https://prove2.me/submissions/01057438-fc55-431c-bd26-66b4c578c1bd

import Definitions.Def_Csg_BackwardInduction
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_MatchingPennies
import Theorems.Thm_Csg_unif2_mem
import Theorems.Thm_Csg_penniesMatrix_payoff_row
import Theorems.Thm_Csg_penniesMatrix_payoff_col
import Theorems.Thm_Csg_MatrixGame_value_unique


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution : penniesMatrix.value = 0 := by
  have huu : penniesMatrix.payoff unif2 unif2 = 0 := penniesMatrix_payoff_row unif2
  have hrow : ∀ p' ∈ stdSimplex ℝ (Fin 2),
      penniesMatrix.payoff unif2 unif2 ≤ penniesMatrix.payoff p' unif2 := fun p' _ =>
    le_of_eq (huu.trans (penniesMatrix_payoff_row p').symm)
  have hcol : ∀ q' ∈ stdSimplex ℝ (Fin 2),
      penniesMatrix.payoff unif2 q' ≤ penniesMatrix.payoff unif2 unif2 := fun q' _ =>
    le_of_eq ((penniesMatrix_payoff_col q').trans huu.symm)
  have hval := penniesMatrix.value_unique unif2_mem unif2_mem hrow hcol
  rw [← hval]
  exact huu
end Csg
