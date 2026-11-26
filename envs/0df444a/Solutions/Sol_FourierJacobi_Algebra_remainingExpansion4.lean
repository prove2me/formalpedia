-- Prove2me | solution 1 for FourierJacobi.Algebra.remainingExpansion4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:09:47.169068+00:00
-- url     : https://prove2.me/submissions/7ac09627-d005-4100-8248-2f4310eba7f1

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
    weylRemainingFactors t a b d 4 = evalCoefficients d (wrCoeffs4 t a b) := by
  simp only [weylRemainingFactors, evalCoefficients, wrCoeffs4, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.reduceFinMk, Fin.val_zero, Fin.val_succ]
  unfold wr4_0 wr4_1 wr4_2 wr4_3 wr4_4 wr4_5 wr4_6
  norm_num
  all_goals grind only
end FourierJacobi.Algebra
