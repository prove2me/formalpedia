-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmG_antitone
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:23:35.579592+00:00
-- url     : https://prove2.me/submissions/f2777818-d692-4d2c-aea5-c71ce17b09c3

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
theorem _root_.solution {n : ℕ} (ν : Fin n → ℕ) (h : ∀ i, nuNext ν i ≤ ν i) : Antitone ν := by
  intro i j hij
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  simp only [Fin.mk_le_mk] at hij
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ k hik ih =>
    have h1 := h ⟨k, by omega⟩
    rw [bmG_nuNext_of_succ ν ⟨k, by omega⟩ ⟨k + 1, hj⟩ rfl] at h1
    exact le_trans h1 (ih (by omega))
end Formalism.BranchingDeterminantCap
