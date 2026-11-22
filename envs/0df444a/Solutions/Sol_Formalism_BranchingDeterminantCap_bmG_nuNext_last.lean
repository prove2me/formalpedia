-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmG_nuNext_last
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:02:16.087846+00:00
-- url     : https://prove2.me/submissions/51866a3e-ff19-4b13-a5c4-2c562a55ad1e

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
theorem _root_.solution {n : ℕ} (ν : Fin n → ℕ) (i : Fin n) (h : ¬ i.val + 1 < n) : nuNext ν i = 0 := by
  unfold nuNext
  rw [dif_neg h]
end Formalism.BranchingDeterminantCap
