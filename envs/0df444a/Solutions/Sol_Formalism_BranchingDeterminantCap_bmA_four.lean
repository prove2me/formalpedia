-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmA_four
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:34:39.986581+00:00
-- url     : https://prove2.me/submissions/8be27006-48b2-4d4b-9abb-39c32cd02917

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmA_adj
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmA_four_mid
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
    (p p' : Fin n) (hp : p'.val = p.val + 1) (α β : Fin n → Fin n) :
    bmM E u α β - bmM E u (α ∘ Equiv.swap p p') (β ∘ Equiv.swap p p') =
      bmM E u (α ∘ Equiv.swap p p') β - bmM E u α (β ∘ Equiv.swap p p') := by
  have hne : p ≠ p' := by intro h; rw [h] at hp; omega
  obtain ⟨L, Rr, hL⟩ := bmA_adj (fun k => bmF E u k (α k) (β k)) p p' hp
  have key : ∀ (α' β' : Fin n → Fin n), (∀ k, k ≠ p → k ≠ p' → α' k = α k ∧ β' k = β k) →
      bmM E u α' β' = L * (bmF E u p (α' p) (β' p) * bmF E u p' (α' p') (β' p')) * Rr := by
    intro α' β' h
    rw [← hL]
    unfold bmM
    congr 2
    funext k
    by_cases h1 : k = p'
    · subst h1; simp
    · rw [Function.update_of_ne h1]
      by_cases h2 : k = p
      · subst h2; simp
      · rw [Function.update_of_ne h2, (h k h2 h1).1, (h k h2 h1).2]
  rw [key α β (fun k _ _ => ⟨rfl, rfl⟩),
    key (α ∘ Equiv.swap p p') (β ∘ Equiv.swap p p') (fun k h1 h2 => by
      simp [Equiv.swap_apply_of_ne_of_ne h1 h2]),
    key (α ∘ Equiv.swap p p') β (fun k h1 h2 => by simp [Equiv.swap_apply_of_ne_of_ne h1 h2]),
    key α (β ∘ Equiv.swap p p') (fun k h1 h2 => by simp [Equiv.swap_apply_of_ne_of_ne h1 h2])]
  simp only [Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
  rw [← mul_sub_right_distrib, ← mul_sub_left_distrib, ← mul_sub_right_distrib, ← mul_sub_left_distrib,
    bmA_four_mid E u hE p p' hp]
end Formalism.BranchingDeterminantCap
