-- Prove2me | solution 1 for FourierJacobi.Algebra.remainingExpansion2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:08:44.410431+00:00
-- url     : https://prove2.me/submissions/8d6aa3e3-bc7a-4c89-9927-684719378120

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
    weylRemainingFactors t a b d 2 = evalCoefficients d (wrCoeffs2 t a b) := by
  simp only [weylRemainingFactors, evalCoefficients, wrCoeffs2, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.reduceFinMk, Fin.val_zero, Fin.val_succ]
  unfold wr2_0 wr2_1 wr2_2 wr2_3 wr2_4 wr2_5 wr2_6
  norm_num
  all_goals grind only
end FourierJacobi.Algebra
