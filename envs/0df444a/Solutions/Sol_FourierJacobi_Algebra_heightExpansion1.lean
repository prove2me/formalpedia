-- Prove2me | solution 1 for FourierJacobi.Algebra.heightExpansion1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:08:22.427467+00:00
-- url     : https://prove2.me/submissions/e948a61c-6f47-494d-bde1-d755d06e0bfd

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
    weylHeight1 t a b d = evalCoefficients d (whCoeffs1 t a b) := by
  simp only [evalCoefficients, whCoeffs1, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.reduceFinMk, Fin.val_zero, Fin.val_succ]
  unfold weylHeight1 wh1_0 wh1_1 wh1_2 wh1_3 wh1_4
  norm_num
  all_goals grind only
end FourierJacobi.Algebra
