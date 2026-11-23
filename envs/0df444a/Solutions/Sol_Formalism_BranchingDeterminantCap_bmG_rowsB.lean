-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmG_rowsB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:00.079877+00:00
-- url     : https://prove2.me/submissions/e386715f-baa7-41fd-a0b1-af091e7b30b8

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
theorem _root_.solution {n : ℕ} (i : Fin n) :
    (rowsB i : Fin (i.val + 1) → Fin (n + 1)) =
      fun p => if h : p.val < i.val then (Fin.castLE (by omega : i.val ≤ n) ⟨p.val, h⟩).castSucc
        else Fin.last n := by
  funext p
  simp only [rowsB]
  by_cases h : p.val < i.val
  · rw [if_pos h, dif_pos h]
    rfl
  · rw [if_neg h, dif_neg h]
end Formalism.BranchingDeterminantCap
