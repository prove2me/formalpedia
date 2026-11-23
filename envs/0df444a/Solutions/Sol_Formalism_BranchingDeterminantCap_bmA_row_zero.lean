-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmA_row_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:30.788822+00:00
-- url     : https://prove2.me/submissions/d0b52397-2014-43d3-b32b-2ccec11504f1

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
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution (E : Fin n → Fin n → Module.End R M) (u : ℤ)
    (h2 : ∀ x : Module.End R M, x + x = 0 → x = 0) (c β : Fin n → Fin n) (k l : Fin n) (hkl : k ≠ l)
    (hc : c k = c l) :
    ∑ α : Equiv.Perm (Fin n), ((Equiv.Perm.sign α : ℤˣ) : ℤ) • bmM E u (c ∘ α) β = 0 := by
  set S : Module.End R M := ∑ α : Equiv.Perm (Fin n), ((Equiv.Perm.sign α : ℤˣ) : ℤ) • bmM E u (c ∘ α) β with hS
  have hcs : c ∘ Equiv.swap k l = c := by
    funext x
    by_cases h1 : x = k
    · subst h1; simp [hc]
    · by_cases h3 : x = l
      · subst h3; simp [hc]
      · simp [Equiv.swap_apply_of_ne_of_ne h1 h3]
  have h3 : S = - S := by
    conv_lhs => rw [hS, ← Equiv.sum_comp (Equiv.mulLeft (Equiv.swap k l))]
    rw [hS, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Equiv.coe_mulLeft, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hkl, Equiv.Perm.coe_mul,
      ← Function.comp_assoc, hcs]
    simp
  exact h2 S (by nth_rewrite 1 [h3]; simp)
end Formalism.BranchingDeterminantCap
