-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.TieLDA.length_quot_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:59:45.64736+00:00
-- url     : https://prove2.me/submissions/ff1839f0-c48f-43dc-920a-d463dc38fe6e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_TieLDA
import Theorems.Thm_Formalism_L2_Pj_QAt_TieLDA_Phi_tmul
import Theorems.Thm_Formalism_L2_Pj_QAt_TieLDA_Phi_range
import Theorems.Thm_Formalism_L2_Pj_QAt_TieLDA_Phi_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.L2.Pj.QAt.TieLDA
open TensorProduct Module
variable {K K₁ : Type*} [Field K] [Field K₁] [Algebra K K₁]
attribute [local instance] modT
attribute [local instance] modR
variable {U : Type*} [AddCommGroup U] [Module K U]
variable {R : Type*} [CommRing R] [Algebra R K] [Module R U] [IsScalarTower R K U]
variable (T : Subring K₁) [Algebra R T]
  (hRT : ∀ r : R, ((algebraMap R T r : T) : K₁) = algebraMap K K₁ (algebraMap R K r))
variable [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K]
include hRT
namespace Formalism.L2.Pj.QAt.TieLDA
theorem _root_.solution (X Y : Submodule R U) (hX : X.FG) (hYX : Y ≤ X) :
    Module.length T (↥(Submodule.span T (tm K K₁ '' (X : Set U))) ⧸
        (Submodule.span T (tm K K₁ '' (Y : Set U))).comap
          (Submodule.span T (tm K K₁ '' (X : Set U))).subtype) =
      Module.length T (T ⊗[R] (X ⧸ Y.comap X.subtype)) := by
  classical
  let Y' := Y.comap X.subtype
  let Ψ : T ⊗[R] X →ₗ[T] T ⊗[R] (X ⧸ Y') := Y'.mkQ.baseChange T
  have h1 : (Ψ : T ⊗[R] X → T ⊗[R] (X ⧸ Y')) = Y'.mkQ.lTensor T := LinearMap.baseChange_eq_ltensor _
  have hΨ : Function.Surjective Ψ := by
    rw [h1]
    exact LinearMap.lTensor_surjective T (Submodule.mkQ_surjective Y')
  let ι' : T ⊗[R] Y' →ₗ[T] T ⊗[R] X := Y'.subtype.baseChange T
  have h2 : (ι' : T ⊗[R] Y' → T ⊗[R] X) = Y'.subtype.lTensor T := LinearMap.baseChange_eq_ltensor _
  have hker : LinearMap.ker Ψ = LinearMap.range ι' := by
    ext z
    have hex := lTensor_exact T (LinearMap.exact_subtype_mkQ Y') (Submodule.mkQ_surjective Y') z
    rw [LinearMap.mem_ker, LinearMap.mem_range, h1, hex, Set.mem_range, h2]
  let e1 : T ⊗[R] X ≃ₗ[T] Submodule.span T (tm K K₁ '' (X : Set U)) :=
    (LinearEquiv.ofInjective (Phi T hRT X) (Phi_injective T hRT X hX)).trans
      (LinearEquiv.ofEq _ _ (Phi_range T hRT X))
  have he1 : ∀ z, ((e1 z : Submodule.span T (tm K K₁ '' (X : Set U))) : K₁ ⊗[K] U) = Phi T hRT X z := by
    intro z
    rfl
  have hY : ∀ z, Phi T hRT X z ∈ Submodule.span T (tm K K₁ '' (Y : Set U)) ↔ z ∈ LinearMap.range ι' := by
    intro z
    constructor
    · intro hz
      have hle : Submodule.span T (tm K K₁ '' (Y : Set U)) ≤ (LinearMap.range ι').map (Phi T hRT X) := by
        rw [Submodule.span_le]
        rintro _ ⟨y, hy, rfl⟩
        refine ⟨ι' ((1 : T) ⊗ₜ ⟨⟨y, hYX hy⟩, hy⟩), ⟨_, rfl⟩, ?_⟩
        show Phi T hRT X ((1 : T) ⊗ₜ ⟨y, hYX hy⟩) = tm K K₁ y
        rw [Phi_tmul]
        simp
      obtain ⟨w, hw, hwz⟩ := hle hz
      rw [← Phi_injective T hRT X hX hwz]
      exact hw
    · rintro ⟨w, rfl⟩
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul t y =>
        show Phi T hRT X (t ⊗ₜ (y : X)) ∈ _
        rw [Phi_tmul]
        exact Submodule.smul_mem _ t (Submodule.subset_span ⟨(y : X), y.2, rfl⟩)
      | add a c ha hc =>
        rw [map_add, map_add]
        exact Submodule.add_mem _ ha hc
  have hmap : ((Submodule.span T (tm K K₁ '' (Y : Set U))).comap
      (Submodule.span T (tm K K₁ '' (X : Set U))).subtype).map (e1.symm : _ →ₗ[T] _) = LinearMap.range ι' := by
    ext z
    rw [Submodule.mem_map_equiv, LinearEquiv.symm_symm, Submodule.mem_comap, Submodule.subtype_apply, he1]
    exact hY z
  exact ((Submodule.Quotient.equiv _ _ e1.symm hmap).trans
    ((Submodule.quotEquivOfEq _ _ hker.symm).trans (Ψ.quotKerEquivOfSurjective hΨ))).length_eq
end Formalism.L2.Pj.QAt.TieLDA
