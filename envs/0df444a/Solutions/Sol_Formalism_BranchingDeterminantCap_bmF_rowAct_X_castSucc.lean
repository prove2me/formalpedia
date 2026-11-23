-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmF_rowAct_X_castSucc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:54.668219+00:00
-- url     : https://prove2.me/submissions/e1ac5d2e-d41a-4d83-b94a-01da7d4982a2

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_rowAction_X_sum
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_extM_castSucc
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_extM_castSucc_last
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
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution (R : Type*) [CommRing R] {n : ℕ} (g : Matrix (Fin n) (Fin n) R) (a s : Fin n) :
    rowAct R (extM R g) (X (a.castSucc, s) : BP R n) = ∑ b : Fin n, C (g a b) * X (b.castSucc, s) := by
  rw [rowAction_X_sum, Fin.sum_univ_castSucc]
  simp [bmF_extM_castSucc, bmF_extM_castSucc_last]
end Formalism.BranchingDeterminantCap
