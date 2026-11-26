-- Prove2me | solution 1 for FourierJacobi.Algebra.heightExpansion6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:10:41.614028+00:00
-- url     : https://prove2.me/submissions/4e4ba69c-e131-49c0-81c6-53c9fd798310

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
    weylHeight6 t a b d = evalCoefficients d (whCoeffs6 t a b) := by
  simp only [evalCoefficients, whCoeffs6, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.reduceFinMk, Fin.val_zero, Fin.val_succ]
  unfold weylHeight6 wh6_0 wh6_1 wh6_2 wh6_3 wh6_4
  norm_num
  all_goals grind only
end FourierJacobi.Algebra
