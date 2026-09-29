-- Prove2me | solution 1 for GaloisRepAdic.isStrictOrdinaryAt_baseChangeAlong
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/33ad2a78-ded5-50f3-9222-1250c4480020

import Mathlib
import Definitions.Def_GaloisRep_StrictOrdinary
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_isStrictOrdinaryAt_baseChangeAlong

set_option autoImplicit false

namespace P2mStrictBC

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
  (φ : A →+* B) (hφ : IsLocalHom φ) (ρ : GaloisRepAdic A)

noncomputable def tm (b : B) (v : ρ.V) : (ρ.baseChangeAlong φ hφ).V :=
  letI : Algebra A B := φ.toAlgebra
  b ⊗ₜ[A] v

theorem tm_add (b : B) (v w : ρ.V) : tm φ hφ ρ b (v + w) = tm φ hφ ρ b v + tm φ hφ ρ b w := by
  letI : Algebra A B := φ.toAlgebra
  show b ⊗ₜ[A] (v + w) = b ⊗ₜ[A] v + b ⊗ₜ[A] w
  exact TensorProduct.tmul_add b v w

theorem tm_sub (b : B) (v w : ρ.V) : tm φ hφ ρ b (v - w) = tm φ hφ ρ b v - tm φ hφ ρ b w := by
  letI : Algebra A B := φ.toAlgebra
  show b ⊗ₜ[A] (v - w) = b ⊗ₜ[A] v - b ⊗ₜ[A] w
  exact TensorProduct.tmul_sub b v w

theorem tm_smul (b : B) (c : A) (v : ρ.V) : tm φ hφ ρ b (c • v) = φ c • tm φ hφ ρ b v := by
  letI : Algebra A B := φ.toAlgebra
  show b ⊗ₜ[A] (c • v) = φ c • (b ⊗ₜ[A] v)
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, ← smul_eq_mul,
    TensorProduct.smul_tmul']
  rfl

theorem smul_tm (b b' : B) (v : ρ.V) : b' • tm φ hφ ρ b v = tm φ hφ ρ (b' * b) v := by
  letI : Algebra A B := φ.toAlgebra
  show b' • (b ⊗ₜ[A] v) = (b' * b) ⊗ₜ[A] v
  rw [TensorProduct.smul_tmul', smul_eq_mul]

theorem rho_tm (σ : Γ) (b : B) (v : ρ.V) :
    (ρ.baseChangeAlong φ hφ).ρ σ (tm φ hφ ρ b v) = tm φ hφ ρ b (ρ.ρ σ v) := by
  letI : Algebra A B := φ.toAlgebra
  show (ρ.ρ σ).baseChange B (b ⊗ₜ[A] v) = b ⊗ₜ[A] (ρ.ρ σ v)
  exact LinearMap.baseChange_tmul _ _ _

theorem tm_induction {C : (ρ.baseChangeAlong φ hφ).V → Prop} (h0 : C 0)
    (ht : ∀ (b : B) (v : ρ.V), C (tm φ hφ ρ b v)) (hadd : ∀ x y, C x → C y → C (x + y))
    (x : (ρ.baseChangeAlong φ hφ).V) : C x := by
  letI : Algebra A B := φ.toAlgebra
  induction x using TensorProduct.induction_on with
  | zero => exact h0
  | tmul b v => exact ht b v
  | add x y hx hy => exact hadd x y hx hy

noncomputable def bcBasis (e : Module.Basis (Fin 2) A ρ.V) : Module.Basis (Fin 2) B (ρ.baseChangeAlong φ hφ).V :=
  letI : Algebra A B := φ.toAlgebra
  Algebra.TensorProduct.basis B e

theorem bcBasis_apply (e : Module.Basis (Fin 2) A ρ.V) (i : Fin 2) :
    bcBasis φ hφ ρ e i = tm φ hφ ρ 1 (e i) := by
  letI : Algebra A B := φ.toAlgebra
  show Algebra.TensorProduct.basis B e i = (1 : B) ⊗ₜ[A] e i
  exact Algebra.TensorProduct.basis_apply e i

theorem tm_mem_span (w : ρ.V) (c : B) {v : ρ.V} (hv : v ∈ A ∙ w) :
    tm φ hφ ρ c v ∈ B ∙ tm φ hφ ρ 1 w := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
  have e1 : tm φ hφ ρ c w = c • tm φ hφ ρ 1 w := by rw [smul_tm, mul_one]
  rw [tm_smul, e1]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))

end P2mStrictBC

open P2mStrictBC in
theorem solution
    {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (φ : A →+* B) (hφ : IsLocalHom φ) (ρ : GaloisRepAdic A)
    {p : ℕ} (h : ρ.IsStrictOrdinaryAt p) : (ρ.baseChangeAlong φ hφ).IsStrictOrdinaryAt p := by
  obtain ⟨hpA, h⟩ := h
  refine ⟨?_, fun P hP => ?_⟩
  ·
    have hnat : ((p : ℕ) : B) = φ (p : A) := by rw [map_natCast]
    rw [hnat]
    haveI := hφ
    exact map_nonunit φ (p : A) hpA
  obtain ⟨L, ⟨b, rfl⟩, hD, hI, hS⟩ := h P hP

  set w : (ρ.baseChangeAlong φ hφ).V := tm φ hφ ρ 1 (b 0) with hw
  have key : ∀ (c : B) {v : ρ.V}, v ∈ A ∙ b 0 → tm φ hφ ρ c v ∈ B ∙ w :=
    fun c v hv => tm_mem_span φ hφ ρ (b 0) c hv
  refine ⟨B ∙ w, ⟨bcBasis φ hφ ρ b, by rw [bcBasis_apply]⟩, ?_, ?_, ?_⟩
  ·
    intro σ hσ v hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul, hw, rho_tm]
    exact Submodule.smul_mem _ _ (key 1 (hD σ hσ _ (Submodule.mem_span_singleton_self _)))
  ·
    intro σ hσ v
    refine tm_induction φ hφ ρ (C := fun v => (ρ.baseChangeAlong φ hφ).ρ σ v - v ∈ B ∙ w)
      (by rw [map_zero, sub_zero]; exact Submodule.zero_mem _) (fun c u => ?_)
      (fun x y hx hy => ?_) v
    · rw [rho_tm, ← tm_sub]
      exact key c (hI σ hσ u)
    · rw [map_add, add_sub_add_comm]
      exact Submodule.add_mem _ hx hy
  ·
    intro σ hσ
    obtain ⟨x, z, hx, hz, hc⟩ := hS σ hσ
    refine ⟨φ x, φ z, ?_, ?_, ?_⟩
    · intro v hv
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
      rw [map_smul, hw, rho_tm, hx _ (Submodule.mem_span_singleton_self _), tm_smul, smul_smul,
        smul_smul, mul_comm]
    · intro v
      refine tm_induction φ hφ ρ
        (C := fun v => (ρ.baseChangeAlong φ hφ).ρ σ v - φ z • v ∈ B ∙ w)
        (by rw [map_zero, smul_zero, sub_zero]; exact Submodule.zero_mem _) (fun c u => ?_)
        (fun x y hx' hy' => ?_) v
      · rw [rho_tm, ← tm_smul, ← tm_sub]
        exact key c (hz u)
      · rw [map_add, smul_add, add_sub_add_comm]
        exact Submodule.add_mem _ hx' hy'
    · intro n a hμ
      obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (hc n a hμ)
      refine Ideal.mem_span_singleton'.mpr ⟨φ t, ?_⟩
      have e1 : φ x - (a : B) * φ z = φ (x - (a : A) * z) := by
        rw [map_sub, map_mul, map_natCast]
      rw [e1, ← ht, map_mul, map_natCast]

end S_GaloisRepAdic_isStrictOrdinaryAt_baseChangeAlong
end P2MW
export P2MW.S_GaloisRepAdic_isStrictOrdinaryAt_baseChangeAlong (solution)
