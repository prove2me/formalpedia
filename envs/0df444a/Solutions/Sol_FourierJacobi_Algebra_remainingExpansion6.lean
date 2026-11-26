-- Prove2me | solution 1 for FourierJacobi.Algebra.remainingExpansion6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:10:52.172259+00:00
-- url     : https://prove2.me/submissions/6627102c-f2de-4171-93ca-c0e5969381d4

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
    weylRemainingFactors t a b d 6 = evalCoefficients d (wrCoeffs6 t a b) := by
  simp only [weylRemainingFactors, evalCoefficients, wrCoeffs6, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.reduceFinMk, Fin.val_zero, Fin.val_succ]
  unfold wr6_0 wr6_1 wr6_2 wr6_3 wr6_4 wr6_5 wr6_6
  norm_num
  all_goals grind only
end FourierJacobi.Algebra
