-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmG_shapeDeg_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:27:45.073628+00:00
-- url     : https://prove2.me/submissions/b7d67a10-7afe-4e5f-ab8e-72bf956c8ecc

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
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
theorem _root_.solution {n K : ℕ} (sz : Fin (K + 1) → ℕ) (t : Fin n) :
    shapeDeg sz t = (if t.val < sz 0 then 1 else 0) + shapeDeg (fun k : Fin K => sz k.succ) t := by
  simp only [shapeDeg, Finset.card_filter, Fin.sum_univ_succ]
end Formalism.BranchingDeterminantCap
