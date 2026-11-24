-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.restrict_roots_to_subfield
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:14:17.818029+00:00
-- url     : https://prove2.me/submissions/14f9f83b-34f8-4e66-87b3-5649039c703b

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_RestrictRoots
import Theorems.Thm_Formalism_GaloisIrreducibility_rr_roots_pow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.GaloisIrreducibility
open Module Polynomial
section SlopeTestRemainingChoices
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
end SlopeTestRemainingChoices
private lemma coe_restrict_pow_apply' {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (A : Module.End K V) (S : Submodule K V) (hS : ∀ x ∈ S, A x ∈ S) (k : ℕ) (x : S) :
    (((A.restrict hS) ^ k) x : V) = (A ^ k) x := by
  induction k with
  | zero => simp
  | succ k ihk =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply,
      LinearMap.restrict_coe_apply, ihk]
private lemma charpoly_restrict_dvd_charpoly {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (τ : Module.End K V) (W : Submodule K V) (hτ : ∀ v ∈ W, τ v ∈ W) :
    (τ.restrict hτ).charpoly ∣ τ.charpoly := by
  classical
  obtain ⟨Q, hWQ⟩ := Submodule.exists_isCompl W
  obtain ⟨e, he⟩ : ∃ e : (W × Q) ≃ₗ[K] V, e = Submodule.prodEquivOfIsCompl W Q hWQ := ⟨_, rfl⟩
  have he1 : ∀ x : W, e.symm (x : V) = (x, 0) := fun x => by
    rw [he]; exact Submodule.prodEquivOfIsCompl_symm_apply_left W Q hWQ x
  have he2 : ∀ x : W, e (x, 0) = (x : V) := fun x => by
    rw [← he1 x, LinearEquiv.apply_symm_apply]
  have bW := Module.finBasis K W
  have bQ := Module.finBasis K Q
  have key : ∀ j, (e.symm.conj τ) ((bW.prod bQ) (Sum.inl j)) = ((τ.restrict hτ) (bW j), 0) := by
    intro j
    have hb : (bW.prod bQ) (Sum.inl j) = (bW j, 0) := by simp [Module.Basis.prod_apply]
    rw [hb, LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.coe_coe, LinearEquiv.symm_symm, he2, ← LinearMap.restrict_coe_apply τ hτ, he1]
  have h21 : (LinearMap.toMatrix (bW.prod bQ) (bW.prod bQ) (e.symm.conj τ)).toBlocks₂₁ = 0 := by
    ext i j
    simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply, LinearMap.toMatrix_apply, key,
      Module.Basis.prod_repr_inr, map_zero, Finsupp.coe_zero, Pi.zero_apply]
  have h11 : (LinearMap.toMatrix (bW.prod bQ) (bW.prod bQ) (e.symm.conj τ)).toBlocks₁₁ =
      LinearMap.toMatrix bW bW (τ.restrict hτ) := by
    ext i j
    simp only [Matrix.toBlocks₁₁, Matrix.of_apply, LinearMap.toMatrix_apply, key,
      Module.Basis.prod_repr_inl]
  rw [← LinearEquiv.charpoly_conj e.symm τ, ← LinearMap.charpoly_toMatrix (e.symm.conj τ) (bW.prod bQ),
    ← LinearMap.charpoly_toMatrix (τ.restrict hτ) bW,
    ← Matrix.fromBlocks_toBlocks (LinearMap.toMatrix (bW.prod bQ) (bW.prod bQ) (e.symm.conj τ)),
    h21, h11, Matrix.charpoly_fromBlocks_zero₂₁]
  exact dvd_mul_right _ _
end Formalism.GaloisIrreducibility
end

set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility
open Module Polynomial
namespace Formalism.GaloisIrreducibility
theorem _root_.solution : RestrictRoots := by
  unfold RestrictRoots
  intro K V _ _ _ _ _ τ F q hF W hτ hFW
  have hFW' : ∀ v ∈ W, (F : V →ₗ[K] V) v ∈ W := hFW
  have hinj : Function.Injective ((F : V →ₗ[K] V).restrict hFW') := by
    intro x y hxy
    apply Subtype.ext
    apply F.injective
    have h := congrArg Subtype.val hxy
    simpa only [LinearMap.restrict_coe_apply, LinearEquiv.coe_coe] using h
  have hbij : Function.Bijective ((F : V →ₗ[K] V).restrict hFW') :=
    ⟨hinj, LinearMap.surjective_of_injective hinj⟩
  obtain ⟨eW, heW⟩ : ∃ eW : W ≃ₗ[K] W, ∀ x, eW x = ((F : V →ₗ[K] V).restrict hFW') x :=
    ⟨LinearEquiv.ofBijective _ hbij, fun x => rfl⟩
  have hconj : eW.conj (τ.restrict hτ) = (τ.restrict hτ) ^ q := by
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := eW.surjective x
    rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    apply Subtype.ext
    simp only [heW, LinearMap.restrict_coe_apply, coe_restrict_pow_apply', LinearEquiv.coe_coe]
    exact hF y
  constructor
  · exact Polynomial.roots.le_of_dvd (LinearMap.charpoly_monic τ).ne_zero
      (charpoly_restrict_dvd_charpoly τ W hτ)
  · have h1 := rr_roots_pow q (finrank K W) W rfl (τ.restrict hτ)
    rw [← hconj, LinearEquiv.charpoly_conj] at h1
    exact h1.symm
end Formalism.GaloisIrreducibility
