-- Prove2me | solution 1 for FourierJacobi.Algebra.remainingExpansion7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:11:12.515813+00:00
-- url     : https://prove2.me/submissions/bca5ff8b-bbcc-4307-8f11-0c7bab4e19d3

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
    weylRemainingFactors t a b d 7 = evalCoefficients d (wrCoeffs7 t a b) := by
  simp only [weylRemainingFactors, evalCoefficients, wrCoeffs7, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.reduceFinMk, Fin.val_zero, Fin.val_succ]
  unfold wr7_0 wr7_1 wr7_2 wr7_3 wr7_4 wr7_5 wr7_6
  norm_num
  all_goals grind only
end FourierJacobi.Algebra
