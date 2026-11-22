-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.rowAction_X_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:45:17.982688+00:00
-- url     : https://prove2.me/submissions/219a681b-7d5a-40f4-a8e5-a24864c17e95

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution (R : Type*) [CommRing R] {r n : ℕ} (g : Matrix (Fin r) (Fin r) R) (v : Fin r × Fin n) :
    rowAct R g (X v) = ∑ b : Fin r, C (g v.1 b) * X (b, v.2) := by
  rw [rowAct, aeval_X]
end Formalism.BranchingDeterminantCap
