-- Prove2me | solution 1 for Formalism.REAL.inner_positionAction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:45:04.886786+00:00
-- url     : https://prove2.me/submissions/fc423be1-c8b3-4037-9ed9-3bbad4ad224b

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero
import Theorems.Thm_Formalism_REAL_factorAction_apply
import Theorems.Thm_Formalism_REAL_sum_update_involution
import Theorems.Thm_Formalism_REAL_indexArray_inner
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open scoped InnerProductSpace
open Finset
noncomputable section
namespace Formalism.REAL
section U3Basic
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n j : ℕ}
end U3Basic
section U3Inner
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n j : ℕ}
private theorem sum_update_ite_eq_sum_update_ite_of_involution {X M : Type*} [Fintype X] [DecidableEq X] [AddCommMonoid M] (i : Fin j)
    (σ τ τ' : X → X) (hσ : ∀ x, σ (σ x) = x) (P Q : X → Prop) [DecidablePred P] [DecidablePred Q]
    (hτ : ∀ x, P x → σ x = τ x) (hτ' : ∀ x, Q x → σ x = τ' x) (hQ : ∀ x, Q x ↔ P (σ x))
    (f : (Fin j → X) → (Fin j → X) → M) :
    ∑ α : Fin j → X, (if P (α i) then f (Function.update α i (τ (α i))) α else 0) =
      ∑ β : Fin j → X, (if Q (β i) then f β (Function.update β i (τ' (β i))) else 0) := by
  have h1 : (∑ α : Fin j → X, (if P (α i) then f (Function.update α i (τ (α i))) α else 0)) =
      ∑ α : Fin j → X, (if P (α i) then f (Function.update α i (σ (α i))) α else 0) := by
    refine Finset.sum_congr rfl fun α _ => ?_
    by_cases h : P (α i)
    · rw [if_pos h, if_pos h, hτ _ h]
    · rw [if_neg h, if_neg h]
  rw [h1, sum_update_involution i σ hσ P f]
  refine Finset.sum_congr rfl fun β _ => ?_
  by_cases h : Q (β i)
  · rw [if_pos ((hQ _).1 h), if_pos h, hτ' _ h]
  · rw [if_neg (fun h' => h ((hQ _).2 h')), if_neg h]
end U3Inner
section U3Cas
variable {W : Type*} [AddCommGroup W] [Module ℂ W] {n : ℕ}
end U3Cas
section U3CasArr
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n j : ℕ}
end U3CasArr
section U3Perm
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n j : ℕ}
end U3Perm
section U3Succ
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n j : ℕ}
end U3Succ
section U3Stable
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n j : ℕ}
end U3Stable
section U3Sym
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n j : ℕ}
end U3Sym
section U3NPos
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n j : ℕ}
end U3NPos
end Formalism.REAL
end
end

set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n j : ℕ}
namespace Formalism.REAL
theorem _root_.solution (i : Fin j) (c d : Fin n) (F G : Arr V n j) :
    ⟪factorAction i c d F, G⟫_ℂ = ⟪F, factorAction i d c G⟫_ℂ := by
  rw [indexArray_inner, indexArray_inner]
  have e1 : ∀ α : Fin j → Fin n × Fin n, ⟪factorAction i c d F α, G α⟫_ℂ =
      (if (α i).1 = c then ⟪F (Function.update α i (d, (α i).2)), G α⟫_ℂ else 0) -
      (if (α i).2 = d then ⟪F (Function.update α i ((α i).1, c)), G α⟫_ℂ else 0) := by
    intro α
    rw [factorAction_apply, inner_sub_left]
    split_ifs <;> simp
  have e2 : ∀ β : Fin j → Fin n × Fin n, ⟪F β, factorAction i d c G β⟫_ℂ =
      (if (β i).1 = d then ⟪F β, G (Function.update β i (c, (β i).2))⟫_ℂ else 0) -
      (if (β i).2 = c then ⟪F β, G (Function.update β i ((β i).1, d))⟫_ℂ else 0) := by
    intro β
    rw [factorAction_apply, inner_sub_right]
    split_ifs <;> simp
  simp only [e1, e2, Finset.sum_sub_distrib]
  congr 1
  · refine sum_update_ite_eq_sum_update_ite_of_involution i (fun p => if p.1 = c then (d, p.2) else if p.1 = d then (c, p.2) else p)
      (fun p => (d, p.2)) (fun p => (c, p.2)) ?_ (fun p => p.1 = c) (fun p => p.1 = d) ?_ ?_ ?_
      (fun x y => ⟪F x, G y⟫_ℂ)
    · rintro ⟨x, y⟩
      by_cases h1 : x = c <;> by_cases h2 : x = d <;> by_cases h3 : d = c <;> simp_all
    · rintro ⟨x, y⟩ h
      simp_all
    · rintro ⟨x, y⟩ h
      by_cases h1 : x = c <;> simp_all
    · rintro ⟨x, y⟩
      by_cases h1 : x = c <;> by_cases h2 : x = d <;> by_cases h3 : d = c <;> simp_all
  · refine sum_update_ite_eq_sum_update_ite_of_involution i (fun p => if p.2 = d then (p.1, c) else if p.2 = c then (p.1, d) else p)
      (fun p => (p.1, c)) (fun p => (p.1, d)) ?_ (fun p => p.2 = d) (fun p => p.2 = c) ?_ ?_ ?_
      (fun x y => ⟪F x, G y⟫_ℂ)
    · rintro ⟨x, y⟩
      by_cases h1 : y = d <;> by_cases h2 : y = c <;> by_cases h3 : c = d <;> simp_all
    · rintro ⟨x, y⟩ h
      simp_all
    · rintro ⟨x, y⟩ h
      by_cases h1 : y = d <;> simp_all
    · rintro ⟨x, y⟩
      by_cases h1 : y = d <;> by_cases h2 : y = c <;> by_cases h3 : c = d <;> simp_all
end Formalism.REAL
