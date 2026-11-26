-- Prove2me | solution 1 for FourierJacobi.Algebra.clearedExpansion7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:11:48.587154+00:00
-- url     : https://prove2.me/submissions/483c58b3-5044-4df2-a7a2-cf2c8c5b37b1

import Definitions.Def_FourierJacobi_Algebra_RegionSum
import Definitions.Def_FourierJacobi_Algebra_EulerFactors
import Definitions.Def_FourierJacobi_Algebra_WeylData
import Theorems.Thm_FourierJacobi_Algebra_heightExpansion7
import Theorems.Thm_FourierJacobi_Algebra_remainingExpansion7

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
variable {K : Type*} [Field K]
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace FourierJacobi.Algebra
theorem _root_.solution (t a b d : K) :
    weylClearedTerms t a b d 7 = evalCoefficients d (wcCoeffs7 t a b) := by
  unfold weylClearedTerms
  simp only [weylHeightNumerators, Matrix.cons_val_zero, Matrix.cons_val_succ]
  rw [heightExpansion7, remainingExpansion7]
  simp only [evalCoefficients, whCoeffs7, wrCoeffs7, wcCoeffs7, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.reduceFinMk, Fin.val_zero, Fin.val_succ]
  unfold wc7_0 wc7_1 wc7_2 wc7_3 wc7_4 wc7_5 wc7_6 wc7_7 wc7_8 wc7_9 wc7_10
  norm_num
  all_goals grind only
end FourierJacobi.Algebra
