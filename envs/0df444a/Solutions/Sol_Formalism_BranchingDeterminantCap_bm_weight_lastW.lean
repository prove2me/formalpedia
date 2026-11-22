-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bm_weight_lastW
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:24:21.802695+00:00
-- url     : https://prove2.me/submissions/a499baad-08b4-4e22-a549-2934713bc0f0

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
theorem _root_.solution {n : ℕ} (m : Fin (n + 1) × Fin n →₀ ℕ) :
    Finsupp.weight (lastW n) m = rowDeg m (Fin.last n) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype m (fun i c => c • lastW n i) (fun _ => zero_smul _ _),
    Fintype.sum_prod_type, Fin.sum_univ_castSucc]
  simp [lastW, rowDeg, Fin.castSucc_ne_last]
end Formalism.BranchingDeterminantCap
