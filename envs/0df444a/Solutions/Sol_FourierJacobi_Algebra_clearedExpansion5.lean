-- Prove2me | solution 1 for FourierJacobi.Algebra.clearedExpansion5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:29:48.292378+00:00
-- url     : https://prove2.me/submissions/844f22aa-3012-4980-b99c-1071156c60cb

import Definitions.Def_FourierJacobi_Algebra_RegionSum
import Definitions.Def_FourierJacobi_Algebra_EulerFactors
import Definitions.Def_FourierJacobi_Algebra_WeylData
import Theorems.Thm_FourierJacobi_Algebra_heightExpansion5
import Theorems.Thm_FourierJacobi_Algebra_remainingExpansion5

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
    weylClearedTerms t a b d 5 = evalCoefficients d (wcCoeffs5 t a b) := by
  unfold weylClearedTerms
  simp only [weylHeightNumerators, Matrix.cons_val_zero, Matrix.cons_val_succ]
  rw [heightExpansion5, remainingExpansion5]
  simp only [evalCoefficients, whCoeffs5, wrCoeffs5, wcCoeffs5, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.reduceFinMk, Fin.val_zero, Fin.val_succ]
  unfold wc5_0 wc5_1 wc5_2 wc5_3 wc5_4 wc5_5 wc5_6 wc5_7 wc5_8 wc5_9 wc5_10
  norm_num
  all_goals grind only
end FourierJacobi.Algebra
