-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmK_antitone
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:55.587867+00:00
-- url     : https://prove2.me/submissions/0d5afed5-a1c0-4c04-a35c-ebb71598b494

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmG_nuNext_of_succ
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
theorem _root_.solution {n : ℕ} (lam sg : Fin n → ℕ) (hIL : bmIL lam sg) : Antitone sg := by
  intro i j hij
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  simp only [Fin.mk_le_mk] at hij
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ k hik ih =>
    have h1 := (hIL ⟨k, by omega⟩).2
    have h2 := (hIL ⟨k + 1, hj⟩).1
    rw [bmG_nuNext_of_succ lam ⟨k, by omega⟩ ⟨k + 1, hj⟩ rfl] at h1
    exact le_trans (le_trans h2 h1) (ih (by omega))
end Formalism.BranchingDeterminantCap
