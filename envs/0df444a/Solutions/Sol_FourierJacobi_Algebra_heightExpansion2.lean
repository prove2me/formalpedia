-- Prove2me | solution 1 for FourierJacobi.Algebra.heightExpansion2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:08:30.936686+00:00
-- url     : https://prove2.me/submissions/2191d66a-ae09-43ae-a551-ae908863a14f

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
    weylHeight2 t a b d = evalCoefficients d (whCoeffs2 t a b) := by
  simp only [evalCoefficients, whCoeffs2, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.reduceFinMk, Fin.val_zero, Fin.val_succ]
  unfold weylHeight2 wh2_0 wh2_1 wh2_2 wh2_3 wh2_4
  norm_num
  all_goals grind only
end FourierJacobi.Algebra
