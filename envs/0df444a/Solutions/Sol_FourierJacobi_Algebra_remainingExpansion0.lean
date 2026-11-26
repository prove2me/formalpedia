-- Prove2me | solution 1 for FourierJacobi.Algebra.remainingExpansion0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:08:21.904655+00:00
-- url     : https://prove2.me/submissions/8a96ec03-2dfc-4b83-af06-7ecc2571b2d3

import Definitions.Def_FourierJacobi_Algebra_RegionSum
import Definitions.Def_FourierJacobi_Algebra_EulerFactors
import Definitions.Def_FourierJacobi_Algebra_WeylData

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
    weylRemainingFactors t a b d 0 = evalCoefficients d (wrCoeffs0 t a b) := by
  simp only [weylRemainingFactors, evalCoefficients, wrCoeffs0, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.reduceFinMk, Fin.val_zero, Fin.val_succ]
  unfold wr0_0 wr0_1 wr0_2 wr0_3 wr0_4 wr0_5 wr0_6
  norm_num
  all_goals grind only
end FourierJacobi.Algebra
