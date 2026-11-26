-- Prove2me | solution 1 for FourierJacobi.Algebra.clearedExpansion2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:14:54.443299+00:00
-- url     : https://prove2.me/submissions/af4b2a2d-f087-4b6f-9c7e-a2d1c23f259f

import Definitions.Def_FourierJacobi_Algebra_RegionSum
import Definitions.Def_FourierJacobi_Algebra_EulerFactors
import Definitions.Def_FourierJacobi_Algebra_WeylData
import Theorems.Thm_FourierJacobi_Algebra_heightExpansion2
import Theorems.Thm_FourierJacobi_Algebra_remainingExpansion2

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
    weylClearedTerms t a b d 2 = evalCoefficients d (wcCoeffs2 t a b) := by
  unfold weylClearedTerms
  simp only [weylHeightNumerators, Matrix.cons_val_zero, Matrix.cons_val_succ]
  rw [heightExpansion2, remainingExpansion2]
  simp only [evalCoefficients, whCoeffs2, wrCoeffs2, wcCoeffs2, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.reduceFinMk, Fin.val_zero, Fin.val_succ]
  unfold wc2_0 wc2_1 wc2_2 wc2_3 wc2_4 wc2_5 wc2_6 wc2_7 wc2_8 wc2_9 wc2_10
  norm_num
  all_goals grind only
end FourierJacobi.Algebra
