-- Prove2me | solution 1 for FourierJacobi.Algebra.clearedExpansion3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:09:56.913941+00:00
-- url     : https://prove2.me/submissions/a4e116bb-4335-4ae2-8e60-ca2310980554

import Definitions.Def_FourierJacobi_Algebra_RegionSum
import Definitions.Def_FourierJacobi_Algebra_EulerFactors
import Definitions.Def_FourierJacobi_Algebra_WeylData
import Theorems.Thm_FourierJacobi_Algebra_heightExpansion3
import Theorems.Thm_FourierJacobi_Algebra_remainingExpansion3

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
    weylClearedTerms t a b d 3 = evalCoefficients d (wcCoeffs3 t a b) := by
  unfold weylClearedTerms
  simp only [weylHeightNumerators, Matrix.cons_val_zero, Matrix.cons_val_succ]
  rw [heightExpansion3, remainingExpansion3]
  simp only [evalCoefficients, whCoeffs3, wrCoeffs3, wcCoeffs3, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.reduceFinMk, Fin.val_zero, Fin.val_succ]
  unfold wc3_0 wc3_1 wc3_2 wc3_3 wc3_4 wc3_5 wc3_6 wc3_7 wc3_8 wc3_9 wc3_10
  norm_num
  all_goals grind only
end FourierJacobi.Algebra
