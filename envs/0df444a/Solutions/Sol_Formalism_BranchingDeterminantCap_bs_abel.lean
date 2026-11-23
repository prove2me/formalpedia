-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bs_abel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:29:04.60882+00:00
-- url     : https://prove2.me/submissions/4100f794-d93e-4858-a5b8-e6a5bac3f267

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchScale
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
open Formalism.REAL
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution (n : ℕ) (x : Fin n → ℤ) :
    ∑ a, (a.val : ℤ) * x a =
      ∑ k ∈ Finset.range n, ((∑ a, x a) - ∑ a : Fin n with a.val < k + 1, x a) := by
  have h1 : ∀ a : Fin n, (a.val : ℤ) = ∑ k ∈ Finset.range n, if k < a.val then (1 : ℤ) else 0 := by
    intro a
    rw [Finset.sum_boole]
    have : (Finset.range n).filter (fun k => k < a.val) = Finset.range a.val := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range]
      have := a.isLt
      omega
    rw [this, Finset.card_range]
  calc ∑ a, (a.val : ℤ) * x a
      = ∑ a : Fin n, ∑ k ∈ Finset.range n, (if k < a.val then x a else 0) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        conv_lhs => rw [h1 a]
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        split_ifs <;> simp
    _ = ∑ k ∈ Finset.range n, ∑ a : Fin n, (if k < a.val then x a else 0) := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_filter, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        by_cases h : k < a.val
        · rw [if_pos h, if_neg (by omega)]; ring
        · rw [if_neg h, if_pos (by omega)]; ring
end Formalism.BranchingDeterminantCap
