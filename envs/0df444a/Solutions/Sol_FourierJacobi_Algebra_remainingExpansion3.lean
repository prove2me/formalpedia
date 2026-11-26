-- Prove2me | solution 1 for FourierJacobi.Algebra.remainingExpansion3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:09:17.756555+00:00
-- url     : https://prove2.me/submissions/0383bcd9-5bcf-4f5b-8542-6d82c0c68b3a

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
    weylRemainingFactors t a b d 3 = evalCoefficients d (wrCoeffs3 t a b) := by
  simp only [weylRemainingFactors, evalCoefficients, wrCoeffs3, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.reduceFinMk, Fin.val_zero, Fin.val_succ]
  unfold wr3_0 wr3_1 wr3_2 wr3_3 wr3_4 wr3_5 wr3_6
  norm_num
  all_goals grind only
end FourierJacobi.Algebra
