-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmG_nuNext_of_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:31:43.515659+00:00
-- url     : https://prove2.me/submissions/223103ed-b1ae-4b53-bf8b-b91639ff1aeb

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
theorem _root_.solution {n : ℕ} (ν : Fin n → ℕ) (i j : Fin n) (h : j.val = i.val + 1) :
    nuNext ν i = ν j := by
  have hc : i.val + 1 < n := by
    have := j.isLt
    omega
  unfold nuNext
  rw [dif_pos hc]
  congr 1
  exact Fin.ext h.symm
end Formalism.BranchingDeterminantCap
