-- Prove2me | solution 1 for FourierJacobi.Algebra.clearedExpansion0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:08:58.762322+00:00
-- url     : https://prove2.me/submissions/02282bb5-4368-473e-aa8f-8c46b56e4c2a

import Definitions.Def_FourierJacobi_Algebra_RegionSum
import Definitions.Def_FourierJacobi_Algebra_EulerFactors
import Definitions.Def_FourierJacobi_Algebra_WeylData
import Theorems.Thm_FourierJacobi_Algebra_heightExpansion0
import Theorems.Thm_FourierJacobi_Algebra_remainingExpansion0

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
    weylClearedTerms t a b d 0 = evalCoefficients d (wcCoeffs0 t a b) := by
  unfold weylClearedTerms
  simp only [weylHeightNumerators, Matrix.cons_val_zero, Matrix.cons_val_succ]
  rw [heightExpansion0, remainingExpansion0]
  simp only [evalCoefficients, whCoeffs0, wrCoeffs0, wcCoeffs0, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.reduceFinMk, Fin.val_zero, Fin.val_succ]
  unfold wc0_0 wc0_1 wc0_2 wc0_3 wc0_4 wc0_5 wc0_6 wc0_7 wc0_8 wc0_9 wc0_10
  norm_num
  all_goals grind only
end FourierJacobi.Algebra
