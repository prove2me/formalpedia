-- Prove2me | solution 1 for Csg.penniesMatrix_payoff_col
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:12:08.063022+00:00
-- url     : https://prove2.me/submissions/965ee2b8-2263-4f14-821a-417f6184ac17

import Definitions.Def_Csg_BackwardInduction
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_MatchingPennies
import Theorems.Thm_Csg_CSG_bwInd_zero
attribute [local simp] Csg.CSG.bwInd_zero


section
namespace Csg
private theorem penniesMatrix_col_sum_zero (j : Fin 2) : ∑ i, penniesMatrix.A i j = 0 := by
  fin_cases j <;> simp [penniesMatrix, Fin.sum_univ_two]
end Csg
end

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (q' : Fin 2 → ℝ) : penniesMatrix.payoff unif2 q' = 0 := by
  simp only [MatrixGame.payoff_eq_sum_mul', unif2, ← Finset.mul_sum, penniesMatrix_col_sum_zero,
    mul_zero, zero_mul, Finset.sum_const_zero]
end Csg
