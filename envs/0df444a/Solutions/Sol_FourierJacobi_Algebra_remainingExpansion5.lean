-- Prove2me | solution 1 for FourierJacobi.Algebra.remainingExpansion5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:10:36.16051+00:00
-- url     : https://prove2.me/submissions/120e9931-6d56-48f4-bf58-26d29fd9cd5b

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
    weylRemainingFactors t a b d 5 = evalCoefficients d (wrCoeffs5 t a b) := by
  simp only [weylRemainingFactors, evalCoefficients, wrCoeffs5, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.reduceFinMk, Fin.val_zero, Fin.val_succ]
  unfold wr5_0 wr5_1 wr5_2 wr5_3 wr5_4 wr5_5 wr5_6
  norm_num
  all_goals grind only
end FourierJacobi.Algebra
