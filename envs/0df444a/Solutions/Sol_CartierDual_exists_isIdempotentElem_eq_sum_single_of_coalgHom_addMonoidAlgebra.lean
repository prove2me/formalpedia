-- Prove2me | solution 1 for CartierDual.exists_isIdempotentElem_eq_sum_single_of_coalgHom_addMonoidAlgebra
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/f6ee6ad4-2150-5e71-a80b-99e6d5a4e5d0

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CartierDual_exists_isIdempotentElem_eq_sum_single_of_coalgHom_addMonoidAlgebra

set_option autoImplicit false

universe u v w

open IsLocalRing
open scoped TensorProduct

open Coalgebra in
theorem solution
    {S : Type u} [CommRing S] {B : Type v} [CommRing B] [Bialgebra S B] [Module.Finite S B] [Module.Free S B]
    (M : Type w) [Fintype M] [DecidableEq M]
    (f : B →ₗc[S] AddMonoidAlgebra S M) :
    ∃ e : M → CartierDual S B,
      (∀ m, IsIdempotentElem (e m)) ∧ (∀ a b, a ≠ b → e a * e b = 0) ∧ ∑ m, e m = 1 ∧
      ∀ b : B, f b = ∑ m, AddMonoidAlgebra.single m (e m b) := by
  classical

  let L : M → Module.Dual S B := fun m =>
    ((Finsupp.lapply m).comp (AddMonoidAlgebra.coeffLinearEquiv S).toLinearMap).comp
      (f : B →ₗ[S] AddMonoidAlgebra S M)
  let e : M → CartierDual S B := fun m => CartierDual.ofDual S B (L m)
  have he : ∀ m b, e m b = (f b).coeff m := fun m b => rfl

  let ev : B → (CartierDual S B →+ S) := fun b =>
    { toFun := fun φ => φ b, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hev : ∀ b φ, ev b φ = φ b := fun _ _ => rfl

  have hrepr : ∀ b : B, f b = ∑ m, AddMonoidAlgebra.single m ((f b).coeff m) := fun b =>
    (AddMonoidAlgebra.coeffLinearEquiv S).injective (by
      simp only [map_sum, AddMonoidAlgebra.coeffLinearEquiv_apply, AddMonoidAlgebra.coeff_single]
      exact (Finsupp.univ_sum_single (f b).coeff).symm)
  have hreprL : ∀ b : B, (f : B →ₗ[S] AddMonoidAlgebra S M) b =
      ∑ m, AddMonoidAlgebra.single m ((f b).coeff m) :=
    fun b => hrepr b

  have key : ∀ (a c : M) (x : B), (e a * e c) x = if a = c then e a x else 0 := by
    intro a c x
    rw [CartierDual.mul_apply]
    simp only [CartierDual.toDual_ofDual, e]

    have hnat : (TensorProduct.dualDistrib S B B (L a ⊗ₜ[S] L c)) =
        (TensorProduct.dualDistrib S (AddMonoidAlgebra S M) (AddMonoidAlgebra S M)
          (((Finsupp.lapply a).comp (AddMonoidAlgebra.coeffLinearEquiv S).toLinearMap) ⊗ₜ[S]
            ((Finsupp.lapply c).comp (AddMonoidAlgebra.coeffLinearEquiv S).toLinearMap))).comp
          (TensorProduct.map (f : B →ₗ[S] AddMonoidAlgebra S M) (f : B →ₗ[S] AddMonoidAlgebra S M)) := by
      apply TensorProduct.ext'
      intro u v
      simp [TensorProduct.dualDistrib_apply, L]
    rw [hnat, LinearMap.comp_apply, ← LinearMap.comp_apply (TensorProduct.map _ _) comul,
      CoalgHomClass.map_comp_comul, LinearMap.comp_apply, hreprL x, map_sum, map_sum]
    simp only [AddMonoidAlgebra.comul_single, CommSemiring.comul_apply, TensorProduct.map_tmul,
      TensorProduct.dualDistrib_apply]

    have hR : ((CartierDual.ofDual S B) (L a)) x = (f x).coeff a := rfl
    rw [hR]
    change ∑ m, (AddMonoidAlgebra.single m (1 : S)).coeff a *
      (AddMonoidAlgebra.single m ((f x).coeff m)).coeff c = _
    simp only [AddMonoidAlgebra.coeff_single]
    by_cases hac : a = c
    · subst hac
      rw [if_pos rfl, Finset.sum_eq_single a]
      · simp [Finsupp.single_apply]
      · intro m _ hma
        simp [Finsupp.single_apply, hma]
      · intro h; exact absurd (Finset.mem_univ a) h
    · rw [if_neg hac]
      refine Finset.sum_eq_zero (fun m _ => ?_)
      by_cases hma : m = a
      · subst hma; simp [Finsupp.single_apply, hac]
      · simp [Finsupp.single_apply, hma]
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  ·
    intro m
    apply CartierDual.ext
    intro x
    rw [key]
    simp
  ·
    intro a c hac
    apply CartierDual.ext
    intro x
    rw [key, if_neg hac]
    rfl
  ·
    apply CartierDual.ext
    intro x
    rw [← hev x, map_sum]
    simp only [hev, he, CartierDual.one_apply]

    have h1 : (∑ m, (f x).coeff m) = counit (R := S) (f x) := by
      conv_rhs => rw [hrepr x]
      rw [map_sum]
      simp [AddMonoidAlgebra.counit_single, CommSemiring.counit_apply]
    rw [h1, CoalgHomClass.counit_comp_apply]
  · intro b
    simp only [he]
    exact hrepr b

end S_CartierDual_exists_isIdempotentElem_eq_sum_single_of_coalgHom_addMonoidAlgebra
end P2MW
export P2MW.S_CartierDual_exists_isIdempotentElem_eq_sum_single_of_coalgHom_addMonoidAlgebra (solution)
