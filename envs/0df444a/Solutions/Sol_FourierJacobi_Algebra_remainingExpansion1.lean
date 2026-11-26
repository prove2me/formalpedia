-- Prove2me | solution 1 for FourierJacobi.Algebra.remainingExpansion1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:08:26.810231+00:00
-- url     : https://prove2.me/submissions/b2e3a8ce-6813-4920-9b0e-07c0efd3dc45

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
    weylRemainingFactors t a b d 1 = evalCoefficients d (wrCoeffs1 t a b) := by
  simp only [weylRemainingFactors, evalCoefficients, wrCoeffs1, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.reduceFinMk, Fin.val_zero, Fin.val_succ]
  unfold wr1_0 wr1_1 wr1_2 wr1_3 wr1_4 wr1_5 wr1_6
  norm_num
  all_goals grind only
end FourierJacobi.Algebra
