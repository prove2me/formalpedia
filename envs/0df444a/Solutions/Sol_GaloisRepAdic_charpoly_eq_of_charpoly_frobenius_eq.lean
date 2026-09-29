-- Prove2me | solution 1 for GaloisRepAdic.charpoly_eq_of_charpoly_frobenius_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/db8844a9-5031-5fdc-a8eb-0d3efc1fbc52

import Definitions.Def_GaloisRep_Adic
import Theorems.Thm_FrobeniusDensity_statement
import Theorems.Thm_FrobeniusDensity_exists_frobenius_conj_pow_of_statement
import Theorems.Thm_Matrix_trace_pow_eq_of_trace_eq_of_det_eq
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.RingTheory.Filtration
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_charpoly_eq_of_charpoly_frobenius_eq
p2m_attr_erase "instance" "FrobeniusDensity.liesOver_ratBelow AlgebraicClosure.Rat.isGalois"

set_option autoImplicit false

open Polynomial Module

namespace RT2DenAux4

lemma repr_mem_of_mem_ideal_smul_top {A : Type} [CommRing A] {V : Type} [AddCommGroup V]
    [Module A V] {ι : Type} (b : Basis ι A V) (I : Ideal A) {x : V}
    (hx : x ∈ I • (⊤ : Submodule A V)) (i : ι) : b.repr x i ∈ I := by
  rw [← b.span_eq] at hx
  obtain ⟨a, haI, rfl⟩ := (Submodule.mem_ideal_smul_span_iff_exists_sum I (⇑b) _).mp hx
  have h : (a.sum fun i c => c • b i) = b.repr.symm a := by
    rw [Basis.repr_symm_apply, Finsupp.linearCombination_apply]
  rw [h, LinearEquiv.apply_symm_apply]
  exact haI i

lemma toMatrix_map_quotient_eq_one {A : Type} [CommRing A] {V : Type} [AddCommGroup V]
    [Module A V] {ι : Type} [Fintype ι] [DecidableEq ι] (b : Basis ι A V) (I : Ideal A)
    {f : Module.End A V} (hf : ∀ v : V, f v - v ∈ I • (⊤ : Submodule A V)) :
    (LinearMap.toMatrix b b f).map (Ideal.Quotient.mk I) = 1 := by
  ext i j
  rw [Matrix.map_apply, LinearMap.toMatrix_apply]
  have hmem : b.repr (f (b j)) i - b.repr (b j) i ∈ I := by
    have h : b.repr (f (b j)) i - b.repr (b j) i = b.repr (f (b j) - b j) i := by
      rw [map_sub, Finsupp.sub_apply]
    rw [h]
    exact repr_mem_of_mem_ideal_smul_top b I (hf (b j)) i
  have hq : Ideal.Quotient.mk I (b.repr (f (b j)) i) = Ideal.Quotient.mk I (b.repr (b j) i) :=
    Ideal.Quotient.eq.mpr hmem
  rw [hq, Basis.repr_self_apply]
  by_cases h : j = i
  · subst h; simp
  · simp [h, Ne.symm h]

lemma charpoly_mul_map_quotient_eq {A : Type} [CommRing A] {V : Type} [AddCommGroup V]
    [Module A V] [Module.Free A V] [Module.Finite A V] (I : Ideal A) (f g : Module.End A V)
    (hg : ∀ v : V, g v - v ∈ I • (⊤ : Submodule A V)) :
    (LinearMap.charpoly (f * g)).map (Ideal.Quotient.mk I) =
      (LinearMap.charpoly f).map (Ideal.Quotient.mk I) := by
  classical
  let b := Module.Free.chooseBasis A V
  rw [← LinearMap.charpoly_toMatrix (f * g) b, ← LinearMap.charpoly_toMatrix f b,
    ← Matrix.charpoly_map _ (Ideal.Quotient.mk I), ← Matrix.charpoly_map _ (Ideal.Quotient.mk I),
    LinearMap.toMatrix_mul b, Matrix.map_mul, toMatrix_map_quotient_eq_one b I hg, mul_one]

private lemma _root_.RT2DenAux4.charpoly_conj {A : Type} [CommRing A] {V : Type} [AddCommGroup V] [Module A V]
    [Module.Free A V] [Module.Finite A V] {G : Type} [Group G] (ρ : G →* Module.End A V)
    (γ x : G) : LinearMap.charpoly (ρ (γ * x * γ⁻¹)) = LinearMap.charpoly (ρ x) := by
  have h₁ : (ρ γ).comp (ρ γ⁻¹) = LinearMap.id := by
    rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl
  have h₂ : (ρ γ⁻¹).comp (ρ γ) = LinearMap.id := by
    rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl
  have he : ρ (γ * x * γ⁻¹) = (LinearEquiv.ofLinear (ρ γ) (ρ γ⁻¹) h₁ h₂).conj (ρ x) := by
    apply LinearMap.ext; intro v
    simp only [map_mul, Module.End.mul_apply, LinearEquiv.conj_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.ofLinear_apply, LinearEquiv.ofLinear_symm_apply]
  rw [he, LinearEquiv.charpoly_conj]

p2m_export "RT2DenAux4" "charpoly_conj"

lemma charpoly_map_quotient_eq_pow_of_fixes {A : Type} [CommRing A] [IsLocalRing A]
    (ρ : GaloisRepAdic A) (I : Ideal A) {L : IntermediateField ℚ (AlgebraicClosure ℚ)}
    (hL : ∀ σ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ' x = x) →
      ∀ v : ρ.V, ρ.ρ σ' v - v ∈ I • (⊤ : Submodule A ρ.V))
    {σ τ γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} {j : ℕ}
    (hfix : ∀ x ∈ L, σ x = (γ * τ ^ j * γ⁻¹) x) :
    (LinearMap.charpoly (ρ.ρ σ)).map (Ideal.Quotient.mk I) =
      (LinearMap.charpoly ((ρ.ρ τ) ^ j)).map (Ideal.Quotient.mk I) := by
  set c := γ * τ ^ j * γ⁻¹ with hc
  have hσ : σ = c * (c⁻¹ * σ) := by rw [mul_inv_cancel_left]
  have hfixc : ∀ x ∈ L, (c⁻¹ * σ) x = x := by
    intro x hx
    rw [AlgEquiv.mul_apply, hfix x hx, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  have hmain := charpoly_mul_map_quotient_eq I (ρ.ρ c) (ρ.ρ (c⁻¹ * σ)) (hL _ hfixc)
  rw [← map_mul, ← hσ] at hmain
  rw [hmain, hc, charpoly_conj ρ.ρ γ (τ ^ j), map_pow]

lemma det_map_quotient_eq_pow_of_fixes {A : Type} [CommRing A] [IsLocalRing A]
    (ρ : GaloisRepAdic A) (I : Ideal A) {L : IntermediateField ℚ (AlgebraicClosure ℚ)}
    (hL : ∀ σ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ' x = x) →
      ∀ v : ρ.V, ρ.ρ σ' v - v ∈ I • (⊤ : Submodule A ρ.V))
    {σ τ γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} {j : ℕ}
    (hfix : ∀ x ∈ L, σ x = (γ * τ ^ j * γ⁻¹) x) :
    Ideal.Quotient.mk I (LinearMap.det (ρ.ρ σ)) =
      Ideal.Quotient.mk I (LinearMap.det (ρ.ρ τ) ^ j) := by
  have h := charpoly_map_quotient_eq_pow_of_fixes ρ I hL hfix
  have h0 : Ideal.Quotient.mk I ((LinearMap.charpoly (ρ.ρ σ)).coeff 0) =
      Ideal.Quotient.mk I ((LinearMap.charpoly ((ρ.ρ τ) ^ j)).coeff 0) := by
    have hc := congrArg (fun P => P.coeff 0) h
    simpa [Polynomial.coeff_map] using hc
  have hd1 : LinearMap.det (ρ.ρ σ) = (LinearMap.charpoly (ρ.ρ σ)).coeff 0 := by
    rw [LinearMap.det_eq_sign_charpoly_coeff, ρ.finrank_eq, neg_one_sq, one_mul]
  have hd2 : LinearMap.det ((ρ.ρ τ) ^ j) = (LinearMap.charpoly ((ρ.ρ τ) ^ j)).coeff 0 := by
    rw [LinearMap.det_eq_sign_charpoly_coeff, ρ.finrank_eq, neg_one_sq, one_mul]
  calc Ideal.Quotient.mk I (LinearMap.det (ρ.ρ σ))
      = Ideal.Quotient.mk I ((LinearMap.charpoly (ρ.ρ σ)).coeff 0) := by rw [hd1]
    _ = Ideal.Quotient.mk I ((LinearMap.charpoly ((ρ.ρ τ) ^ j)).coeff 0) := h0
    _ = Ideal.Quotient.mk I (LinearMap.det ((ρ.ρ τ) ^ j)) := by rw [hd2]
    _ = Ideal.Quotient.mk I (LinearMap.det (ρ.ρ τ) ^ j) := by rw [map_pow]

lemma det_sub_mem_of_forall_eq {A : Type} [CommRing A] [IsLocalRing A]
    (ρ : GaloisRepAdic A) (I : Ideal A) {L : IntermediateField ℚ (AlgebraicClosure ℚ)}
    (hL : ∀ σ'' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ'' x = x) →
      ∀ v : ρ.V, ρ.ρ σ'' v - v ∈ I • (⊤ : Submodule A ρ.V))
    {σ σ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hagree : ∀ x ∈ L, σ x = σ' x) :
    LinearMap.det (ρ.ρ σ) - LinearMap.det (ρ.ρ σ') ∈ I := by
  have hσ : σ = σ' * (σ'⁻¹ * σ) := by rw [mul_inv_cancel_left]
  have hfixc : ∀ x ∈ L, (σ'⁻¹ * σ) x = x := by
    intro x hx
    rw [AlgEquiv.mul_apply, hagree x hx, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  have hmain := charpoly_mul_map_quotient_eq I (ρ.ρ σ') (ρ.ρ (σ'⁻¹ * σ)) (hL _ hfixc)
  rw [← map_mul, ← hσ] at hmain
  have h0 : Ideal.Quotient.mk I ((LinearMap.charpoly (ρ.ρ σ)).coeff 0) =
      Ideal.Quotient.mk I ((LinearMap.charpoly (ρ.ρ σ')).coeff 0) := by
    have hc := congrArg (fun P => P.coeff 0) hmain
    simpa [Polynomial.coeff_map] using hc
  have hd1 : LinearMap.det (ρ.ρ σ) = (LinearMap.charpoly (ρ.ρ σ)).coeff 0 := by
    rw [LinearMap.det_eq_sign_charpoly_coeff, ρ.finrank_eq, neg_one_sq, one_mul]
  have hd2 : LinearMap.det (ρ.ρ σ') = (LinearMap.charpoly (ρ.ρ σ')).coeff 0 := by
    rw [LinearMap.det_eq_sign_charpoly_coeff, ρ.finrank_eq, neg_one_sq, one_mul]
  rw [hd1, hd2]
  exact Ideal.Quotient.eq.mp h0

end RT2DenAux4

open RT2DenAux4 in
open GaloisRepAdic in
theorem solution
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (ρ₁ ρ₂ : GaloisRepAdic A)
    (S : Finset ℕ)
    (hfrob : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∀ (B : ValuationSubring (AlgebraicClosure ℚ))
      (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), B.LiesOverPrime ℓ → B.IsFrobeniusAt τ ℓ →
        LinearMap.charpoly (ρ₁.ρ τ) = LinearMap.charpoly (ρ₂.ρ τ))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    LinearMap.charpoly (ρ₁.ρ σ) = LinearMap.charpoly (ρ₂.ρ σ) := by
  have key : ∀ n : ℕ,
      (LinearMap.charpoly (ρ₁.ρ σ)).map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ n)) =
      (LinearMap.charpoly (ρ₂.ρ σ)).map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ n)) := by
    intro n
    obtain ⟨L₁, hfd₁, h₁⟩ := ρ₁.isAdicContinuous n
    obtain ⟨L₂, hfd₂, h₂⟩ := ρ₂.isAdicContinuous n
    haveI := hfd₁; haveI := hfd₂
    obtain ⟨ℓ, hℓp, hℓS, B, τ, γ, j, hBℓ, hBfrob, hfix⟩ :=
      FrobeniusDensity.exists_frobenius_conj_pow_of_statement
        (fun M hF hN hG => @FrobeniusDensity.statement M hF hN hG) (L₁ ⊔ L₂) σ S
    have hL₁ : ∀ σ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        (∀ x ∈ (L₁ ⊔ L₂ : IntermediateField ℚ (AlgebraicClosure ℚ)), σ' x = x) →
        ∀ v : ρ₁.V, ρ₁.ρ σ' v - v ∈
          (IsLocalRing.maximalIdeal A ^ n) • (⊤ : Submodule A ρ₁.V) :=
      fun σ' hσ' => h₁ σ' fun x hx => hσ' x (SetLike.le_def.mp le_sup_left hx)
    have hL₂ : ∀ σ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        (∀ x ∈ (L₁ ⊔ L₂ : IntermediateField ℚ (AlgebraicClosure ℚ)), σ' x = x) →
        ∀ v : ρ₂.V, ρ₂.ρ σ' v - v ∈
          (IsLocalRing.maximalIdeal A ^ n) • (⊤ : Submodule A ρ₂.V) :=
      fun σ' hσ' => h₂ σ' fun x hx => hσ' x (SetLike.le_def.mp le_sup_right hx)
    have d₁ := charpoly_map_quotient_eq_pow_of_fixes ρ₁ (IsLocalRing.maximalIdeal A ^ n) hL₁ hfix
    have d₂ := charpoly_map_quotient_eq_pow_of_fixes ρ₂ (IsLocalRing.maximalIdeal A ^ n) hL₂ hfix
    have hτ := hfrob ℓ hℓp hℓS B τ hBℓ hBfrob
    have hpow : LinearMap.charpoly ((ρ₁.ρ τ) ^ j) = LinearMap.charpoly ((ρ₂.ρ τ) ^ j) := by
      classical
      let b₁ : Basis (Fin 2) A ρ₁.V := Module.finBasisOfFinrankEq A ρ₁.V ρ₁.finrank_eq
      let b₂ : Basis (Fin 2) A ρ₂.V := Module.finBasisOfFinrankEq A ρ₂.V ρ₂.finrank_eq
      have hM : (LinearMap.toMatrix b₁ b₁ (ρ₁.ρ τ)).charpoly =
          (LinearMap.toMatrix b₂ b₂ (ρ₂.ρ τ)).charpoly := by
        rw [LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix]; exact hτ
      have htr : (LinearMap.toMatrix b₁ b₁ (ρ₁.ρ τ)).trace =
          (LinearMap.toMatrix b₂ b₂ (ρ₂.ρ τ)).trace := by
        rw [Matrix.trace_eq_neg_charpoly_coeff, Matrix.trace_eq_neg_charpoly_coeff, hM]
      have hdet : (LinearMap.toMatrix b₁ b₁ (ρ₁.ρ τ)).det =
          (LinearMap.toMatrix b₂ b₂ (ρ₂.ρ τ)).det := by
        rw [Matrix.det_eq_sign_charpoly_coeff, Matrix.det_eq_sign_charpoly_coeff, hM]
      rw [← LinearMap.charpoly_toMatrix ((ρ₁.ρ τ) ^ j) b₁,
        ← LinearMap.charpoly_toMatrix ((ρ₂.ρ τ) ^ j) b₂,
        ← LinearMap.toMatrix_pow, ← LinearMap.toMatrix_pow,
        Matrix.charpoly_fin_two, Matrix.charpoly_fin_two,
        Matrix.trace_pow_eq_of_trace_eq_of_det_eq htr hdet j,
        Matrix.det_pow, Matrix.det_pow, hdet]
    rw [d₁, d₂, hpow]
  have hbot : (⨅ n : ℕ, IsLocalRing.maximalIdeal A ^ n) = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal A).ne_top
  refine Polynomial.ext fun k => ?_
  rw [← sub_eq_zero, ← Ideal.mem_bot, ← hbot, Submodule.mem_iInf]
  intro n
  have hk := congrArg (fun P => P.coeff k) (key n)
  simp only [Polynomial.coeff_map] at hk
  exact Ideal.Quotient.eq.mp hk

end S_GaloisRepAdic_charpoly_eq_of_charpoly_frobenius_eq
end P2MW
export P2MW.S_GaloisRepAdic_charpoly_eq_of_charpoly_frobenius_eq (solution)
