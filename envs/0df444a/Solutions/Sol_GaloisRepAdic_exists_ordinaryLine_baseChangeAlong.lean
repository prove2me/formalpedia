-- Prove2me | solution 1 for GaloisRepAdic.exists_ordinaryLine_baseChangeAlong
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/0b51844d-c926-5e87-9f93-5946f4a91200

import Mathlib
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_exists_ordinaryLine_baseChangeAlong

set_option autoImplicit false

namespace GaloisRepAdic
p2m_export "GaloisRepAdic" "baseChangeAlong ρ V"
namespace K7OrdinaryLineAux
p2m_open "GaloisRepAdic"

open TensorProduct

theorem mem_span_iff_repr_one_eq_zero {R V : Type} [CommRing R] [AddCommGroup V] [Module R V]
    (b : Module.Basis (Fin 2) R V) (v : V) : v ∈ R ∙ b 0 ↔ b.repr v 1 = 0 := by
  constructor
  · intro hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    simp
  · intro hv
    have := b.sum_repr v
    rw [Fin.sum_univ_two, hv, zero_smul, add_zero] at this
    rw [← this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem forall_sub_smul_mem_span_iff {R V : Type} [CommRing R] [AddCommGroup V] [Module R V]
    (b : Module.Basis (Fin 2) R V) (M : Module.End R V) (z : R) :
    (∀ v, M v - z • v ∈ R ∙ b 0) ↔ b.repr (M (b 0)) 1 = 0 ∧ b.repr (M (b 1)) 1 = z := by
  simp_rw [mem_span_iff_repr_one_eq_zero b]
  constructor
  · intro h
    have h0 := h (b 0)
    have h1 := h (b 1)
    simp at h0 h1
    exact ⟨h0, sub_eq_zero.mp h1⟩
  · rintro ⟨h0, h1⟩ v
    have key : (Finsupp.lapply (1 : Fin 2) ∘ₗ b.repr.toLinearMap) ∘ₗ (M - z • LinearMap.id) = 0 := by
      apply b.ext
      refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
      · simp [h0]
      · simp [h1]
    have := LinearMap.congr_fun key v
    simpa using this

theorem basis_repr_baseChange_apply {A B V : Type} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup V] [Module A V] (b : Module.Basis (Fin 2) A V) (M : Module.End A V)
    (i j : Fin 2) :
    (Algebra.TensorProduct.basis B b).repr
        (M.baseChange B (Algebra.TensorProduct.basis B b j)) i =
      algebraMap A B (b.repr (M (b j)) i) := by
  rw [Algebra.TensorProduct.basis_apply, LinearMap.baseChange_tmul,
    Algebra.TensorProduct.basis_repr_tmul]
  simp

theorem baseChange_mem_span_of_mem_span {A B V : Type} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup V] [Module A V] (b : Module.Basis (Fin 2) A V) (M : Module.End A V)
    (hL : ∀ v ∈ A ∙ b 0, M v ∈ A ∙ b 0) :
    ∀ v ∈ B ∙ Algebra.TensorProduct.basis B b 0,
      M.baseChange B v ∈ B ∙ Algebra.TensorProduct.basis B b 0 := by
  intro v hv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
  rw [map_smul]
  refine Submodule.smul_mem _ _ ?_
  rw [mem_span_iff_repr_one_eq_zero, basis_repr_baseChange_apply,
    (mem_span_iff_repr_one_eq_zero b _).mp (hL _ (Submodule.mem_span_singleton_self _)), map_zero]

theorem forall_baseChange_sub_smul_mem_span {A B V : Type} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup V] [Module A V] (b : Module.Basis (Fin 2) A V) (M : Module.End A V) (z : A)
    (h : ∀ v, M v - z • v ∈ A ∙ b 0) :
    ∀ v, M.baseChange B v - algebraMap A B z • v ∈ B ∙ Algebra.TensorProduct.basis B b 0 := by
  rw [forall_sub_smul_mem_span_iff] at h ⊢
  rw [basis_repr_baseChange_apply, basis_repr_baseChange_apply, h.1, h.2, map_zero]
  exact ⟨rfl, rfl⟩

theorem exists_quotientScalar_of_baseChange {A B V : Type} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup V] [Module A V] (b : Module.Basis (Fin 2) A V) (M : Module.End A V)
    (hL : ∀ v ∈ A ∙ b 0, M v ∈ A ∙ b 0) (z' : B)
    (h' : ∀ v, M.baseChange B v - z' • v ∈ B ∙ Algebra.TensorProduct.basis B b 0) :
    ∃ z : A, (∀ v, M v - z • v ∈ A ∙ b 0) ∧ algebraMap A B z = z' := by
  refine ⟨b.repr (M (b 1)) 1, (forall_sub_smul_mem_span_iff b M _).mpr
    ⟨(mem_span_iff_repr_one_eq_zero b _).mp (hL _ (Submodule.mem_span_singleton_self _)), rfl⟩, ?_⟩
  rw [← basis_repr_baseChange_apply]
  exact ((forall_sub_smul_mem_span_iff _ _ _).mp h').2

end GaloisRepAdic.K7OrdinaryLineAux

theorem solution
    {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (φ : A →+* B) (hφ : IsLocalHom φ) (ρ : GaloisRepAdic A)
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (L : Submodule A ρ.V) (hLb : ∃ b : Module.Basis (Fin 2) A ρ.V, L = A ∙ b 0)
    (hLD : ∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L, ρ.ρ σ v ∈ L)
    (hLI : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ σ v - v ∈ L) :
    ∃ L' : Submodule B (ρ.baseChangeAlong φ hφ).V,
      (∃ b' : Module.Basis (Fin 2) B (ρ.baseChangeAlong φ hφ).V, L' = B ∙ b' 0) ∧
      (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L', (ρ.baseChangeAlong φ hφ).ρ σ v ∈ L') ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : (ρ.baseChangeAlong φ hφ).V,
        (ρ.baseChangeAlong φ hφ).ρ σ v - v ∈ L') ∧
      (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ z : A, (∀ v : ρ.V, ρ.ρ σ v - z • v ∈ L) →
        ∀ v : (ρ.baseChangeAlong φ hφ).V, (ρ.baseChangeAlong φ hφ).ρ σ v - φ z • v ∈ L') ∧
      (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ z' : B,
        (∀ v : (ρ.baseChangeAlong φ hφ).V, (ρ.baseChangeAlong φ hφ).ρ σ v - z' • v ∈ L') →
        ∃ z : A, (∀ v : ρ.V, ρ.ρ σ v - z • v ∈ L) ∧ φ z = z') := by
  letI : Algebra A B := φ.toAlgebra
  obtain ⟨b, rfl⟩ := hLb
  refine ⟨B ∙ Algebra.TensorProduct.basis B b 0, ⟨Algebra.TensorProduct.basis B b, rfl⟩,
    fun σ hσ => ?_, fun σ hσ v => ?_, fun σ hσ z hz v => ?_, fun σ hσ z' hz' => ?_⟩
  · exact GaloisRepAdic.K7OrdinaryLineAux.baseChange_mem_span_of_mem_span b (ρ.ρ σ) (hLD σ hσ)
  · have h1 : ∀ w : ρ.V, ρ.ρ σ w - (1 : A) • w ∈ A ∙ b 0 := fun w => by
      rw [one_smul]; exact hLI σ hσ w
    have := GaloisRepAdic.K7OrdinaryLineAux.forall_baseChange_sub_smul_mem_span
      (B := B) b (ρ.ρ σ) 1 h1 v
    rwa [map_one, one_smul] at this
  · exact GaloisRepAdic.K7OrdinaryLineAux.forall_baseChange_sub_smul_mem_span
      (B := B) b (ρ.ρ σ) z hz v
  · exact GaloisRepAdic.K7OrdinaryLineAux.exists_quotientScalar_of_baseChange
      b (ρ.ρ σ) (hLD σ hσ) z' hz'

end S_GaloisRepAdic_exists_ordinaryLine_baseChangeAlong
end P2MW
export P2MW.S_GaloisRepAdic_exists_ordinaryLine_baseChangeAlong (solution)
