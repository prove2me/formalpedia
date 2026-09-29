-- Prove2me | solution 1 for GaloisRepAdic.trace_eq_of_trace_frobenius_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/c27fb695-f8d3-5aa0-afb1-6b83e4804619

import Mathlib
import Definitions.Def_GaloisRep_Adic
import Theorems.Thm_FrobeniusDensity_exists_isFrobeniusAt_conj_mem_of_le_ker
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_trace_eq_of_trace_frobenius_eq
p2m_attr_erase "instance" "FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false

namespace AdicTraceChebAsm

open IsLocalRing

section General

variable {A : Type} [CommRing A]

theorem repr_mem_of_mem_smul_top {V : Type*} [AddCommGroup V] [Module A V] {ι : Type*}
    (b : Module.Basis ι A V) (I : Ideal A) {v : V} (hv : v ∈ I • (⊤ : Submodule A V)) (i : ι) :
    b.repr v i ∈ I := by
  refine Submodule.smul_induction_on hv (fun a ha w _ => ?_) (fun x y hx hy => ?_)
  · rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ ha
  · rw [map_add, Finsupp.add_apply]
    exact Ideal.add_mem _ hx hy

theorem trace_mem_of_forall_mem {V : Type*} [AddCommGroup V] [Module A V] [Module.Free A V]
    [Module.Finite A V] (I : Ideal A) (f : Module.End A V)
    (hf : ∀ v, f v ∈ I • (⊤ : Submodule A V)) : LinearMap.trace A V f ∈ I := by
  classical
  let b := Module.Free.chooseBasis A V
  rw [LinearMap.trace_eq_matrix_trace A b, Matrix.trace]
  refine Ideal.sum_mem _ fun i _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  exact repr_mem_of_mem_smul_top b I (hf _) i

end General

section Reps

variable {A : Type} [CommRing A] [IsLocalRing A]

def levelStab (ρ : GaloisRepAdic A) (I : Ideal A) :
    Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) where
  carrier := {τ | ∀ v, ρ.ρ τ v - v ∈ I • (⊤ : Submodule A ρ.V)}
  one_mem' := fun v => by
    rw [map_one, Module.End.one_apply, sub_self]; exact Submodule.zero_mem _
  mul_mem' := fun {a b} ha hb v => by
    have h1 : ρ.ρ (a * b) v - v = ρ.ρ a (ρ.ρ b v - v) + (ρ.ρ a v - v) := by
      rw [map_mul, Module.End.mul_apply, map_sub]; abel
    rw [h1]
    refine Submodule.add_mem _ ?_ (ha v)
    have hmap : (I • (⊤ : Submodule A ρ.V)).map (ρ.ρ a) ≤ I • ⊤ := by
      rw [Submodule.map_smul'']; exact Submodule.smul_mono le_rfl le_top
    exact hmap (Submodule.mem_map_of_mem (hb v))
  inv_mem' := fun {a} ha v => by
    have h := ha (ρ.ρ a⁻¹ v)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h
    rw [← Submodule.neg_mem_iff, neg_sub]
    exact h

theorem trace_sub_trace_mem (ρ : GaloisRepAdic A) (I : Ideal A)
    {τ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (h : τ * σ⁻¹ ∈ levelStab ρ I) :
    ρ.trace τ - ρ.trace σ ∈ I := by
  have hτ : τ = (τ * σ⁻¹) * σ := by group
  have hlin : ρ.ρ τ - ρ.ρ σ = (ρ.ρ (τ * σ⁻¹) - 1) * ρ.ρ σ := by
    conv_lhs => rw [hτ]
    rw [map_mul, sub_mul, one_mul]
  unfold GaloisRepAdic.trace
  rw [← map_sub, hlin]
  refine trace_mem_of_forall_mem I _ fun v => ?_
  rw [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply]
  exact h _

theorem trace_conj (ρ : GaloisRepAdic A) (g τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ρ.trace (g * τ * g⁻¹) = ρ.trace τ := by
  unfold GaloisRepAdic.trace
  rw [map_mul, LinearMap.trace_mul_comm, ← map_mul, ← mul_assoc, inv_mul_cancel, one_mul]

theorem exists_frobenius_trace_sub_mem (ρ₁ ρ₂ : GaloisRepAdic A) (S : Finset ℕ) (m : ℕ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∉ S ∧ ∃ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ ∧
      ∃ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt τ ℓ ∧
        ρ₁.trace σ - ρ₁.trace τ ∈ (maximalIdeal A) ^ m ∧
        ρ₂.trace σ - ρ₂.trace τ ∈ (maximalIdeal A) ^ m := by
  obtain ⟨L₁, hL₁fin, hL₁⟩ := ρ₁.isAdicContinuous m
  obtain ⟨L₂, hL₂fin, hL₂⟩ := ρ₂.isAdicContinuous m
  haveI := hL₁fin
  haveI := hL₂fin
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := by convert AlgebraicClosure.instIsAlgClosure ℚ; rfl; rfl
  haveI : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ _
  let L' : IntermediateField ℚ (AlgebraicClosure ℚ) := L₁ ⊔ L₂
  haveI : FiniteDimensional ℚ L' := IntermediateField.finiteDimensional_sup L₁ L₂
  let F : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.normalClosure ℚ L' (AlgebraicClosure ℚ)
  haveI : FiniteDimensional ℚ F := normalClosure.is_finiteDimensional ℚ L' (AlgebraicClosure ℚ)
  haveI : NumberField F := ⟨⟩
  haveI : Normal ℚ F := normalClosure.normal ℚ L' (AlgebraicClosure ℚ)
  haveI : IsGalois ℚ F := ⟨⟩
  let H : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
    levelStab ρ₁ ((maximalIdeal A) ^ m) ⊓ levelStab ρ₂ ((maximalIdeal A) ^ m)
  have hL₁F : L₁ ≤ F := (le_sup_left : L₁ ≤ L').trans (IntermediateField.le_normalClosure L')
  have hL₂F : L₂ ≤ F := (le_sup_right : L₂ ≤ L').trans (IntermediateField.le_normalClosure L')
  have hfix : ∀ x : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      x ∈ (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker →
        ∀ y ∈ F, x y = y := by
    intro x hx y hy
    rw [MonoidHom.mem_ker] at hx
    have h1 := AlgEquiv.restrictNormalHom_apply F x ⟨y, hy⟩
    have h2 := DFunLike.congr_fun hx ⟨y, hy⟩
    rw [AlgEquiv.one_apply] at h2
    have h3 := congrArg (fun z : ↥F => (z : AlgebraicClosure ℚ)) h2
    exact h1.symm.trans h3
  have hker : (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker ≤ H := by
    intro x hx
    exact ⟨hL₁ x fun y hy => hfix x hx y (hL₁F hy), hL₂ x fun y hy => hfix x hx y (hL₂F hy)⟩
  obtain ⟨ℓ, P, τ, g, hℓ, hℓS, hP, hτ, hmem⟩ :=
    FrobeniusDensity.exists_isFrobeniusAt_conj_mem_of_le_ker F hker S σ
  refine ⟨ℓ, hℓ, hℓS, P, hP, τ, hτ, ?_, ?_⟩
  · have h := trace_sub_trace_mem ρ₁ _ hmem.1
    rw [trace_conj] at h
    rw [← Submodule.neg_mem_iff, neg_sub]
    exact h
  · have h := trace_sub_trace_mem ρ₂ _ hmem.2
    rw [trace_conj] at h
    rw [← Submodule.neg_mem_iff, neg_sub]
    exact h

theorem main [IsNoetherianRing A] (ρ₁ ρ₂ : GaloisRepAdic A) (S : Finset ℕ)
    (hfrob : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∀ (B : ValuationSubring (AlgebraicClosure ℚ))
      (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), B.LiesOverPrime ℓ → B.IsFrobeniusAt τ ℓ →
        ρ₁.trace τ = ρ₂.trace τ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ρ₁.trace σ = ρ₂.trace σ := by
  rw [← sub_eq_zero]
  have hmem : ρ₁.trace σ - ρ₂.trace σ ∈ (⨅ m : ℕ, maximalIdeal A ^ m) := by
    refine Ideal.mem_iInf.mpr fun m => ?_
    obtain ⟨ℓ, hℓ, hℓS, P, hP, τ, hτ, h₁, h₂⟩ := exists_frobenius_trace_sub_mem ρ₁ ρ₂ S m σ
    have : ρ₁.trace σ - ρ₂.trace σ =
        (ρ₁.trace σ - ρ₁.trace τ) - (ρ₂.trace σ - ρ₂.trace τ) := by
      rw [hfrob ℓ hℓ hℓS P τ hP hτ]; ring
    rw [this]
    exact Ideal.sub_mem _ h₁ h₂
  rwa [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal A).ne_top,
    Ideal.mem_bot] at hmem

end Reps

end AdicTraceChebAsm

theorem solution
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (ρ₁ ρ₂ : GaloisRepAdic A)
    (S : Finset ℕ)
    (hfrob : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∀ (B : ValuationSubring (AlgebraicClosure ℚ))
      (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), B.LiesOverPrime ℓ → B.IsFrobeniusAt τ ℓ →
        ρ₁.trace τ = ρ₂.trace τ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ρ₁.trace σ = ρ₂.trace σ :=
  AdicTraceChebAsm.main ρ₁ ρ₂ S hfrob σ

end S_GaloisRepAdic_trace_eq_of_trace_frobenius_eq
end P2MW
export P2MW.S_GaloisRepAdic_trace_eq_of_trace_frobenius_eq (solution)
