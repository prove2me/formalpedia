-- Prove2me | solution 1 for FourierJacobi.Algebra.heightExpansion7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:11:07.192964+00:00
-- url     : https://prove2.me/submissions/aa968ffe-822d-4062-8fac-ef0183e82c48

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
    weylHeight7 t a b d = evalCoefficients d (whCoeffs7 t a b) := by
  simp only [evalCoefficients, whCoeffs7, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.reduceFinMk, Fin.val_zero, Fin.val_succ]
  unfold weylHeight7 wh7_0 wh7_1 wh7_2 wh7_3 wh7_4
  norm_num
  all_goals grind only
end FourierJacobi.Algebra
