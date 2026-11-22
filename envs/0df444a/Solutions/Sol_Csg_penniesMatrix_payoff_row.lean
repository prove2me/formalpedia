-- Prove2me | solution 1 for Csg.penniesMatrix_payoff_row
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:12:00.85503+00:00
-- url     : https://prove2.me/submissions/63fa2d4c-f0cb-452d-bf4f-9ec92f9f1878

import Definitions.Def_Csg_BackwardInduction
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_MatchingPennies
import Theorems.Thm_Csg_CSG_bwInd_zero
attribute [local simp] Csg.CSG.bwInd_zero


section
namespace Csg
private theorem penniesMatrix_row_sum_zero (i : Fin 2) : ∑ j, penniesMatrix.A i j = 0 := by
  fin_cases i <;> simp [penniesMatrix, Fin.sum_univ_two]
end Csg
end

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (p' : Fin 2 → ℝ) : penniesMatrix.payoff p' unif2 = 0 := by
  simp only [MatrixGame.payoff_eq_sum_mul, unif2, ← Finset.sum_mul, penniesMatrix_row_sum_zero,
    zero_mul, mul_zero, Finset.sum_const_zero]
end Csg
