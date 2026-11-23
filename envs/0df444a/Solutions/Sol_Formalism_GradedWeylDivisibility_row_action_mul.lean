-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.row_action_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:55:43.206234+00:00
-- url     : https://prove2.me/submissions/77e9b5bb-eee7-43d0-bc82-4869b7e32b10

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_RowActMul
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution : RowActMul := by
  intro R _ k n g h
  apply MvPolynomial.algHom_ext
  intro v
  simp only [AlgHom.comp_apply, rowAct, aeval_X, map_sum, map_mul, aeval_C, Matrix.mul_apply,
    MvPolynomial.algebraMap_eq, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm
end Formalism.GradedWeylDivisibility
