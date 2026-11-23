-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmA_Pi_adj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:37:33.526572+00:00
-- url     : https://prove2.me/submissions/f1882fb1-7e73-4794-953d-1fc83cdb5737

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmA_four
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
    (hE : ∀ i j k l, E i j * E k l - E k l * E i j = (if j = k then E i l else 0) - (if i = l then E k j else 0))
    (h2 : ∀ x : Module.End R M, x + x = 0 → x = 0)
    (p p' : Fin n) (hp : p'.val = p.val + 1) (β : Fin n → Fin n) :
    bmPi E u (β ∘ Equiv.swap p p') = - bmPi E u β := by
  have hne : p ≠ p' := by intro h; rw [h] at hp; omega
  set s := Equiv.swap p p' with hs
  have hsign : ∀ α : Equiv.Perm (Fin n), ((Equiv.Perm.sign (α * s) : ℤˣ) : ℤ) = - ((Equiv.Perm.sign α : ℤˣ) : ℤ) := by
    intro α
    rw [Equiv.Perm.sign_mul, hs, Equiv.Perm.sign_swap hne]; simp

  have h1 : bmPi E u (β ∘ s) = - ∑ α : Equiv.Perm (Fin n), ((Equiv.Perm.sign α : ℤˣ) : ℤ) • bmM E u (α ∘ s) (β ∘ s) := by
    unfold bmPi
    rw [← Equiv.sum_comp (Equiv.mulRight s), ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Equiv.coe_mulRight, hsign, neg_smul, Equiv.Perm.coe_mul]
  set S : Module.End R M := ∑ α : Equiv.Perm (Fin n), ((Equiv.Perm.sign α : ℤˣ) : ℤ) •
      (bmM E u α β - bmM E u (α ∘ s) (β ∘ s)) with hS
  have h3 : S = - S := by
    conv_lhs => rw [hS, ← Equiv.sum_comp (Equiv.mulRight s)]
    rw [hS, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Equiv.coe_mulRight, hsign, neg_smul, Equiv.Perm.coe_mul]
    congr 2
    have hss : ((α : Fin n → Fin n) ∘ s) ∘ s = α := by
      funext k; simp [hs]
    rw [hss, hs, bmA_four E u hE p p' hp α β]
  have h4 : S = 0 := h2 S (by nth_rewrite 1 [h3]; simp)
  have h5 : S = bmPi E u β + bmPi E u (β ∘ s) := by
    rw [h1, hS]
    unfold bmPi
    simp only [smul_sub, Finset.sum_sub_distrib]
    abel
  rw [h4] at h5
  exact (neg_eq_of_add_eq_zero_right h5.symm).symm
end Formalism.BranchingDeterminantCap
