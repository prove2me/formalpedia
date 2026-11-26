-- Prove2me | solution 1 for FourierJacobi.Algebra.clearedExpansion6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:11:33.141973+00:00
-- url     : https://prove2.me/submissions/3a99ed3f-175f-4359-b602-144a326348d4

import Definitions.Def_FourierJacobi_Algebra_RegionSum
import Definitions.Def_FourierJacobi_Algebra_EulerFactors
import Definitions.Def_FourierJacobi_Algebra_WeylData
import Theorems.Thm_FourierJacobi_Algebra_heightExpansion6
import Theorems.Thm_FourierJacobi_Algebra_remainingExpansion6

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
    weylClearedTerms t a b d 6 = evalCoefficients d (wcCoeffs6 t a b) := by
  unfold weylClearedTerms
  simp only [weylHeightNumerators, Matrix.cons_val_zero, Matrix.cons_val_succ]
  rw [heightExpansion6, remainingExpansion6]
  simp only [evalCoefficients, whCoeffs6, wrCoeffs6, wcCoeffs6, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.reduceFinMk, Fin.val_zero, Fin.val_succ]
  unfold wc6_0 wc6_1 wc6_2 wc6_3 wc6_4 wc6_5 wc6_6 wc6_7 wc6_8 wc6_9 wc6_10
  norm_num
  all_goals grind only
end FourierJacobi.Algebra
