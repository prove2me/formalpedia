-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bm_weight_zW
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:04:39.312948+00:00
-- url     : https://prove2.me/submissions/be52c602-cc84-4c56-a663-0153e6bab0f1

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
theorem _root_.solution {n : ℕ} (m : Fin (n + 1) × Fin n →₀ ℕ) (s : Fin n) :
    Finsupp.weight (zW n) m s = (m (Fin.last n, s) : ℤ) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype m (fun i c => c • zW n i) (fun _ => zero_smul _ _), Finset.sum_apply,
    Fintype.sum_prod_type, Fin.sum_univ_castSucc]
  simp [zW, Pi.single_apply, Fin.castSucc_ne_last]
end Formalism.BranchingDeterminantCap
