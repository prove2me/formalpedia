-- Prove2me | solution 1 for FourierJacobi.Algebra.clearedExpansion4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:15:08.643651+00:00
-- url     : https://prove2.me/submissions/d4308c04-b953-4012-afa8-8fc62b60927d

import Definitions.Def_FourierJacobi_Algebra_RegionSum
import Definitions.Def_FourierJacobi_Algebra_EulerFactors
import Definitions.Def_FourierJacobi_Algebra_WeylData
import Theorems.Thm_FourierJacobi_Algebra_heightExpansion4
import Theorems.Thm_FourierJacobi_Algebra_remainingExpansion4

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
    weylClearedTerms t a b d 4 = evalCoefficients d (wcCoeffs4 t a b) := by
  unfold weylClearedTerms
  simp only [weylHeightNumerators, Matrix.cons_val_zero, Matrix.cons_val_succ]
  rw [heightExpansion4, remainingExpansion4]
  simp only [evalCoefficients, whCoeffs4, wrCoeffs4, wcCoeffs4, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.reduceFinMk, Fin.val_zero, Fin.val_succ]
  unfold wc4_0 wc4_1 wc4_2 wc4_3 wc4_4 wc4_5 wc4_6 wc4_7 wc4_8 wc4_9 wc4_10
  norm_num
  all_goals grind only
end FourierJacobi.Algebra
