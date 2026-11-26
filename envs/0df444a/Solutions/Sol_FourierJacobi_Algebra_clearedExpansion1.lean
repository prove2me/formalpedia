-- Prove2me | solution 1 for FourierJacobi.Algebra.clearedExpansion1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:08:59.27614+00:00
-- url     : https://prove2.me/submissions/e89c0f92-ec4f-4fb0-bffa-b1ef5ccec56a

import Definitions.Def_FourierJacobi_Algebra_RegionSum
import Definitions.Def_FourierJacobi_Algebra_EulerFactors
import Definitions.Def_FourierJacobi_Algebra_WeylData
import Theorems.Thm_FourierJacobi_Algebra_heightExpansion1
import Theorems.Thm_FourierJacobi_Algebra_remainingExpansion1

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
    weylClearedTerms t a b d 1 = evalCoefficients d (wcCoeffs1 t a b) := by
  unfold weylClearedTerms
  simp only [weylHeightNumerators, Matrix.cons_val_zero, Matrix.cons_val_succ]
  rw [heightExpansion1, remainingExpansion1]
  simp only [evalCoefficients, whCoeffs1, wrCoeffs1, wcCoeffs1, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.reduceFinMk, Fin.val_zero, Fin.val_succ]
  unfold wc1_0 wc1_1 wc1_2 wc1_3 wc1_4 wc1_5 wc1_6 wc1_7 wc1_8 wc1_9 wc1_10
  norm_num
  all_goals grind only
end FourierJacobi.Algebra
