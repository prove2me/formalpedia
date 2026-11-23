-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmC_tri
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:31.61489+00:00
-- url     : https://prove2.me/submissions/fd9fb93d-48ff-4e94-b831-cbf29df3f311

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
theorem _root_.solution {r n : ℕ} (m : Fin r × Fin n →₀ ℕ) (hm : Interlaced m) (hr : n ≤ r) :
    ∀ (k : ℕ) (j : Fin n), j.val = k → ∀ a : Fin r, a.val < k → m (a, j) = 0 := by
  intro k
  induction k with
  | zero => intro j _ a ha; exact absurd ha (Nat.not_lt_zero _)
  | succ k ih =>
    intro j hj a ha
    have hk : k < n := by have := j.isLt; omega
    have h1 := hm ⟨k, hk⟩ j (by simpa using hj) ⟨k, by omega⟩
    have h0 : (∑ b : Fin r with b < (⟨k, by omega⟩ : Fin r), m (b, (⟨k, hk⟩ : Fin n))) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      rw [Finset.mem_filter] at hb
      exact ih ⟨k, hk⟩ rfl b (by simpa [Fin.lt_def] using hb.2)
    rw [h0, add_zero, Nat.le_zero, Finset.sum_eq_zero_iff] at h1
    exact h1 a (by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, by rw [Fin.le_def]; simp; omega⟩)
end Formalism.BranchingDeterminantCap
