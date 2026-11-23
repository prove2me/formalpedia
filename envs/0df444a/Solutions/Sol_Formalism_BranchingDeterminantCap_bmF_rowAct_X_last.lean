-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmF_rowAct_X_last
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:55.066141+00:00
-- url     : https://prove2.me/submissions/fcc3a65d-e17f-43c5-9a0b-7f07612ed80c

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_rowAction_X_sum
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_extM_last_castSucc
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_extM_last_last
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
theorem _root_.solution (R : Type*) [CommRing R] {n : ℕ} (g : Matrix (Fin n) (Fin n) R) (s : Fin n) :
    rowAct R (extM R g) (X (Fin.last n, s) : BP R n) = X (Fin.last n, s) := by
  rw [rowAction_X_sum, Fin.sum_univ_castSucc]
  simp [bmF_extM_last_castSucc, bmF_extM_last_last]
end Formalism.BranchingDeterminantCap
