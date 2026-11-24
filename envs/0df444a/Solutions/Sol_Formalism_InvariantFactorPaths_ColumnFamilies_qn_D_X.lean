-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qn_D_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:26.76881+00:00
-- url     : https://prove2.me/submissions/7462083c-3d45-474d-8328-dfd8244c0fd9

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementH
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TransposeVariables
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_D_apply
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
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (n : ℕ) (a b : Fin n) (l c : Fin n) :
    qn_D n a b (X (l, c)) = if c = b then X (l, a) else 0 := by
  rw [qn_D_apply]
  simp only [MvPolynomial.pderiv_X, Pi.single_apply, Prod.mk.injEq]
  by_cases hc : c = b
  · subst hc
    simp
  · simp [hc]
end Formalism.InvariantFactorPaths.ColumnFamilies
