-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmG_sumB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:00.276475+00:00
-- url     : https://prove2.me/submissions/3320812a-4d3c-464e-9040-899e632f3a2a

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_sum_single_castLE
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
theorem _root_.solution {n : ℕ} (i : Fin n) :
    (∑ p : Fin (i.val + 1), (Pi.single (rowsB i p) 1 : Fin (n + 1) → ℕ)) =
      initW (n + 1) i.val + Pi.single (Fin.last n) 1 := by
  rw [Fin.sum_univ_castSucc, ← sum_single_castLE (by omega : i.val ≤ n + 1)]
  congr 1
  · refine Finset.sum_congr rfl fun p _ => ?_
    congr 1
    unfold rowsB
    rw [if_pos (by simp)]
    exact Fin.ext rfl
  · congr 1
    unfold rowsB
    rw [if_neg (by simp)]
end Formalism.BranchingDeterminantCap
