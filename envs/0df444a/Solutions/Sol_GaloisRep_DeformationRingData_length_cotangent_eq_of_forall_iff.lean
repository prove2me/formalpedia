-- Prove2me | solution 1 for GaloisRep.DeformationRingData.length_cotangent_eq_of_forall_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/f1561d46-a45f-5937-bcf9-1be39074d7ef

import Definitions.Def_GaloisRep_DeformationRingData
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Length
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_DeformationRingData_length_cotangent_eq_of_forall_iff

set_option autoImplicit false

namespace K2cEngine

open scoped TensorProduct

section BaseChange

variable {A B C : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
  [CommRing C] [IsLocalRing C]

theorem isEquiv_baseChangeAlong_id (ρ : GaloisRepAdic A) (h : IsLocalHom (RingHom.id A)) :
    (ρ.baseChangeAlong (RingHom.id A) h).IsEquiv ρ := by
  let e : A ⊗[A] ρ.V ≃ₗ[A] ρ.V := TensorProduct.lid A ρ.V
  have key : ∀ σ, e.toLinearMap ∘ₗ (ρ.ρ σ).baseChange A = ρ.ρ σ ∘ₗ e.toLinearMap := by
    intro σ
    refine TensorProduct.ext' fun (a : A) (v : ρ.V) => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearMap.baseChange_tmul, e,
      TensorProduct.lid_tmul, map_smul]
  refine ⟨{ toLinearEquiv := e, map_apply := fun σ x => ?_ }⟩
  exact LinearMap.congr_fun (key σ) x

theorem isEquiv_baseChangeAlong_congr (ρ : GaloisRepAdic A) {φ φ' : A →+* B} (e : φ = φ')
    (h : IsLocalHom φ) (h' : IsLocalHom φ') :
    (ρ.baseChangeAlong φ h).IsEquiv (ρ.baseChangeAlong φ' h') := by
  subst e
  exact ⟨GaloisRepAdic.Equiv.refl _⟩

theorem isEquiv_baseChangeAlong_comp (φ : A →+* B) (hφ : IsLocalHom φ) (ψ : B →+* C)
    (hψ : IsLocalHom ψ) (hψφ : IsLocalHom (ψ.comp φ)) (ρ : GaloisRepAdic A) :
    ((ρ.baseChangeAlong φ hφ).baseChangeAlong ψ hψ).IsEquiv (ρ.baseChangeAlong (ψ.comp φ) hψφ) := by
  letI : Algebra A B := φ.toAlgebra
  letI : Algebra B C := ψ.toAlgebra
  letI : Algebra A C := (ψ.comp φ).toAlgebra
  haveI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C ρ.V
  have key : ∀ σ, e.toLinearMap ∘ₗ ((ρ.ρ σ).baseChange B).baseChange C =
      (ρ.ρ σ).baseChange C ∘ₗ e.toLinearMap := by
    intro σ
    refine TensorProduct.AlgebraTensorModule.ext fun (c : C) (y : B ⊗[A] ρ.V) => ?_
    induction y using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.tmul_zero, map_zero]
    | tmul b v =>
      simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearMap.baseChange_tmul, e,
        TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
    | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]
  refine ⟨{ toLinearEquiv := e, map_apply := fun σ x => ?_ }⟩
  exact LinearMap.congr_fun (key σ) x

end BaseChange

section Iso

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
  {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
  {𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}

theorem exists_algEquiv
    (h : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρ : GaloisRepAdic A), 𝒟' ρ ↔ 𝒟₀ ρ)
    (D₀ : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟₀) (D' : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟')
    (θ : D'.R →ₐ[𝒪] D₀.R) (hθ : IsLocalHom (θ : D'.R →+* D₀.R))
    (hθρ : (D'.ρ.baseChangeAlong (θ : D'.R →+* D₀.R) hθ).IsEquiv D₀.ρ) :
    ∃ e : D'.R ≃ₐ[𝒪] D₀.R, (e : D'.R →ₐ[𝒪] D₀.R) = θ := by

  obtain ⟨ψ, ⟨hψ, hψρ⟩, -⟩ := D₀.universal D'.R D'.residue_surjective D'.ρ
    ((h D'.ρ).mp D'.isOfType) D'.residual_isEquiv

  have h₁ : θ.comp ψ = AlgHom.id 𝒪 D₀.R := by
    have hcomp : IsLocalHom ((θ : D'.R →+* D₀.R).comp (ψ : D₀.R →+* D'.R)) := inferInstance
    refine (D₀.universal D₀.R D₀.residue_surjective D₀.ρ D₀.isOfType D₀.residual_isEquiv).unique
      ?_ ?_
    · refine ⟨(by rw [AlgHom.comp_toRingHom]; exact hcomp), ?_⟩
      obtain ⟨e₁⟩ := isEquiv_baseChangeAlong_comp (ψ : D₀.R →+* D'.R) hψ (θ : D'.R →+* D₀.R) hθ
        hcomp D₀.ρ
      obtain ⟨e₂⟩ := hψρ
      obtain ⟨e₃⟩ := hθρ
      obtain ⟨e₀⟩ := isEquiv_baseChangeAlong_congr D₀.ρ (AlgHom.comp_toRingHom θ ψ)
        (by rw [AlgHom.comp_toRingHom]; exact hcomp) hcomp
      exact ⟨e₀.trans (e₁.symm.trans ((e₂.baseChangeAlong _ hθ).trans e₃))⟩
    · refine ⟨(by rw [AlgHom.id_toRingHom]; infer_instance), ?_⟩
      obtain ⟨e₀⟩ := isEquiv_baseChangeAlong_congr D₀.ρ (AlgHom.id_toRingHom 𝒪 D₀.R)
        (by rw [AlgHom.id_toRingHom]; infer_instance) inferInstance
      obtain ⟨e₁⟩ := isEquiv_baseChangeAlong_id D₀.ρ inferInstance
      exact ⟨e₀.trans e₁⟩

  have h₂ : ψ.comp θ = AlgHom.id 𝒪 D'.R := by
    have hcomp : IsLocalHom ((ψ : D₀.R →+* D'.R).comp (θ : D'.R →+* D₀.R)) := inferInstance
    refine (D'.universal D'.R D'.residue_surjective D'.ρ D'.isOfType D'.residual_isEquiv).unique
      ?_ ?_
    · refine ⟨(by rw [AlgHom.comp_toRingHom]; exact hcomp), ?_⟩
      obtain ⟨e₁⟩ := isEquiv_baseChangeAlong_comp (θ : D'.R →+* D₀.R) hθ (ψ : D₀.R →+* D'.R) hψ
        hcomp D'.ρ
      obtain ⟨e₂⟩ := hθρ
      obtain ⟨e₃⟩ := hψρ
      obtain ⟨e₀⟩ := isEquiv_baseChangeAlong_congr D'.ρ (AlgHom.comp_toRingHom ψ θ)
        (by rw [AlgHom.comp_toRingHom]; exact hcomp) hcomp
      exact ⟨e₀.trans (e₁.symm.trans ((e₂.baseChangeAlong _ hψ).trans e₃))⟩
    · refine ⟨(by rw [AlgHom.id_toRingHom]; infer_instance), ?_⟩
      obtain ⟨e₀⟩ := isEquiv_baseChangeAlong_congr D'.ρ (AlgHom.id_toRingHom 𝒪 D'.R)
        (by rw [AlgHom.id_toRingHom]; infer_instance) inferInstance
      obtain ⟨e₁⟩ := isEquiv_baseChangeAlong_id D'.ρ inferInstance
      exact ⟨e₀.trans e₁⟩
  exact ⟨AlgEquiv.ofAlgHom θ ψ h₁ h₂, rfl⟩

end Iso

section Cotangent

variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

noncomputable def cotangentEquivOfAlgEquiv (e : A ≃ₐ[R] B) (J : Ideal B) :
    (J.comap (e : A →ₐ[R] B)).Cotangent ≃ₗ[R] J.Cotangent := by
  refine LinearEquiv.ofLinear
    (Ideal.mapCotangent (J.comap (e : A →ₐ[R] B)) J (e : A →ₐ[R] B) le_rfl)
    (Ideal.mapCotangent J (J.comap (e : A →ₐ[R] B)) (e.symm : B →ₐ[R] A) ?_) ?_ ?_
  · intro b hb
    show e (e.symm b) ∈ J
    rw [e.apply_symm_apply]
    exact hb
  · apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective J x
    rw [LinearMap.comp_apply, Ideal.mapCotangent_toCotangent, Ideal.mapCotangent_toCotangent,
      LinearMap.id_apply]
    congr 1
    ext
    simp
  · apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ x
    rw [LinearMap.comp_apply, Ideal.mapCotangent_toCotangent, Ideal.mapCotangent_toCotangent,
      LinearMap.id_apply]
    congr 1
    ext
    simp

end Cotangent

end K2cEngine

open K2cEngine in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
    {𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
    (h : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρ : GaloisRepAdic A), 𝒟' ρ ↔ 𝒟₀ ρ)
    (D₀ : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟₀) (D' : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟')
    (θ : D'.R →ₐ[𝒪] D₀.R) (hθ : IsLocalHom (θ : D'.R →+* D₀.R))
    (hθρ : (D'.ρ.baseChangeAlong (θ : D'.R →+* D₀.R) hθ).IsEquiv D₀.ρ)
    (x₀ : D₀.R →ₐ[𝒪] 𝒪) :
    Module.length 𝒪 (RingHom.ker (x₀.comp θ)).Cotangent =
      Module.length 𝒪 (RingHom.ker x₀).Cotangent := by
  obtain ⟨e, he⟩ := exists_algEquiv h D₀ D' θ hθ hθρ
  subst he
  have hker : RingHom.ker (x₀.comp (e : D'.R →ₐ[𝒪] D₀.R)) =
      (RingHom.ker x₀).comap (e : D'.R →ₐ[𝒪] D₀.R) :=
    Ideal.ext fun _ => Iff.rfl
  rw [hker]
  exact (cotangentEquivOfAlgEquiv e (RingHom.ker x₀)).length_eq

end S_GaloisRep_DeformationRingData_length_cotangent_eq_of_forall_iff
end P2MW
export P2MW.S_GaloisRep_DeformationRingData_length_cotangent_eq_of_forall_iff (solution)
