-- Prove2me | solution 1 for GaloisRepAdic.exists_stableLine_frobenius_sub_smul_mem_of_isUnipotentOnInertiaAt_of_residual_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/73c440fd-ed06-5a5e-b9ad-644ffd660a3e

import Mathlib
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_exists_stableLine_frobenius_sub_smul_mem_of_isUnipotentOnInertiaAt_of_residual_ne_one

set_option autoImplicit false

open Polynomial TensorProduct

namespace K1G13Brick

variable {A : Type} [CommRing A] [IsLocalRing A]

section LinAlg

variable {V : Type} [AddCommGroup V] [Module A V] [Module.Free A V] [Module.Finite A V]

omit [IsLocalRing A] in

theorem X_sub_one_sq_eq : ((X : A[X]) - 1) ^ 2 = X ^ 2 - C (2 : A) * X + C (1 : A) := by
  have h2 : (C (2 : A) : A[X]) = 2 := map_ofNat C 2
  rw [h2, map_one]
  ring

omit [IsLocalRing A] in

theorem trace_det_of_charpoly [Nontrivial A] (hV : Module.finrank A V = 2) {f : Module.End A V}
    (hf : f.charpoly = (X - 1) ^ 2) :
    LinearMap.trace A V f = 2 ∧ LinearMap.det f = 1 := by
  classical
  let b := Module.finBasisOfFinrankEq A V hV
  have hM : (LinearMap.toMatrix b b f).charpoly = (X - 1) ^ 2 := by
    rw [LinearMap.charpoly_toMatrix, hf]
  have hc1 : ((X : A[X]) ^ 2 - C (2 : A) * X + C (1 : A)).coeff 1 = -2 := by
    simp [coeff_C, coeff_one]
  have hc0 : ((X : A[X]) ^ 2 - C (2 : A) * X + C (1 : A)).coeff 0 = 1 := by
    simp [coeff_C, coeff_one]
  constructor
  · rw [LinearMap.trace_eq_matrix_trace A b, Matrix.trace_eq_neg_charpoly_coeff, hM, X_sub_one_sq_eq,
      Fintype.card_fin, show 2 - 1 = 1 from rfl, hc1, neg_neg]
  · rw [← LinearMap.det_toMatrix b, Matrix.det_eq_sign_charpoly_coeff, hM, X_sub_one_sq_eq,
      Fintype.card_fin, hc0]
    norm_num

omit [IsLocalRing A] in

theorem sub_one_mul_sub_one_eq_zero {f : Module.End A V} (hf : f.charpoly = (X - 1) ^ 2) :
    (f - 1) * (f - 1) = 0 := by
  have hCH := LinearMap.aeval_self_charpoly f
  rw [hf] at hCH
  simpa [sq, sub_mul, mul_sub] using hCH

omit [IsLocalRing A] in

private theorem _root_.K1G13Brick.trace_one (hV : Module.finrank A V = 2) : LinearMap.trace A V 1 = 2 := by
  rw [LinearMap.trace_one, hV]; norm_num

p2m_export "K1G13Brick" "trace_one"
end LinAlg

section Coord

variable {V : Type} [AddCommGroup V] [Module A V]

omit [IsLocalRing A] in
theorem repr_expand (b : Module.Basis (Fin 2) A V) (x : V) :
    x = b.repr x 0 • b 0 + b.repr x 1 • b 1 := by
  conv_lhs => rw [← b.sum_repr x]
  rw [Fin.sum_univ_two]

omit [IsLocalRing A] in
theorem mem_span_iff_repr_one_eq_zero (b : Module.Basis (Fin 2) A V) (x : V) :
    x ∈ A ∙ b 0 ↔ b.repr x 1 = 0 := by
  constructor
  · intro hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    simp
  · intro h
    rw [repr_expand b x, h, zero_smul, add_zero]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

omit [IsLocalRing A] in
theorem repr_of_eq (b : Module.Basis (Fin 2) A V) {x : V} {c₀ c₁ : A}
    (h : x = c₀ • b 0 + c₁ • b 1) : b.repr x 0 = c₀ ∧ b.repr x 1 = c₁ := by
  subst h
  simp

end Coord

section Place

variable (P : ValuationSubring (AlgebraicClosure ℚ))

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem mem_inertiaSubgroupIn_iff (τ : Γ) :
    τ ∈ P.inertiaSubgroupIn ℚ ↔ ∃ h : τ ∈ P.decompositionSubgroup ℚ,
      (⟨τ, h⟩ : P.decompositionSubgroup ℚ) ∈ P.inertiaSubgroup ℚ := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t.2, by simpa using ht⟩
  · rintro ⟨h, ht⟩
    exact ⟨⟨τ, h⟩, ht, rfl⟩

theorem conj_mem_inertiaSubgroupIn {σ τ : Γ} (hσ : σ ∈ P.decompositionSubgroup ℚ)
    (hτ : τ ∈ P.inertiaSubgroupIn ℚ) : σ * τ * σ⁻¹ ∈ P.inertiaSubgroupIn ℚ := by
  rw [mem_inertiaSubgroupIn_iff] at hτ ⊢
  obtain ⟨hτD, hτI⟩ := hτ
  have hmem : σ * τ * σ⁻¹ ∈ P.decompositionSubgroup ℚ :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hσ hτD) (Subgroup.inv_mem _ hσ)
  refine ⟨hmem, ?_⟩
  have hnormal : (P.inertiaSubgroup ℚ).Normal := by
    unfold ValuationSubring.inertiaSubgroup; infer_instance
  have := hnormal.conj_mem ⟨τ, hτD⟩ hτI ⟨σ, hσ⟩
  convert this using 1 <;> rfl

theorem inv_mul_mem_inertiaSubgroupIn_of_isFrobeniusAt {q : ℕ} {σ₀ σ : Γ}
    (h₀ : P.IsFrobeniusAt σ₀ q) (h : P.IsFrobeniusAt σ q) :
    σ₀⁻¹ * σ ∈ P.inertiaSubgroupIn ℚ := by
  rw [mem_inertiaSubgroupIn_iff]
  have hD₀ := h₀.mem_decompositionSubgroup
  have hD := h.mem_decompositionSubgroup
  have hmem : σ₀⁻¹ * σ ∈ P.decompositionSubgroup ℚ :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hD₀) hD
  refine ⟨hmem, ?_⟩
  unfold ValuationSubring.inertiaSubgroup
  rw [MonoidHom.mem_ker]
  have hprod : (⟨σ₀⁻¹ * σ, hmem⟩ : P.decompositionSubgroup ℚ) =
      (⟨σ₀, hD₀⟩ : P.decompositionSubgroup ℚ)⁻¹ * ⟨σ, hD⟩ := rfl
  rw [hprod, map_mul, map_inv]
  have hkey : MulSemiringAction.toRingAut (P.decompositionSubgroup ℚ)
      (IsLocalRing.ResidueField P) ⟨σ₀, hD₀⟩ =
      MulSemiringAction.toRingAut (P.decompositionSubgroup ℚ)
      (IsLocalRing.ResidueField P) ⟨σ, hD⟩ := by
    refine RingEquiv.ext fun x => ?_
    show (⟨σ₀, hD₀⟩ : P.decompositionSubgroup ℚ) • x = (⟨σ, hD⟩ : P.decompositionSubgroup ℚ) • x
    rw [h₀.smul_residue_eq, h.smul_residue_eq]
  rw [hkey, inv_mul_cancel]

end Place

section Main

variable [IsReduced A] (ρ : GaloisRepAdic A)

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
local notation "k" => IsLocalRing.ResidueField A

omit [IsReduced A] in
theorem residual_apply (σ : Γ) : ρ.residual.ρ σ = (ρ.ρ σ).baseChange k := rfl

omit [IsReduced A] in

theorem exists_tmul_ne_zero {τ₀ : Γ} (hτ₀ : ρ.residual.ρ τ₀ ≠ 1) :
    ∃ v₁ : ρ.V, (1 : k) ⊗ₜ[A] ((ρ.ρ τ₀ - 1) v₁) ≠ 0 := by
  by_contra hall
  push Not at hall
  apply hτ₀
  rw [residual_apply]
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c v =>
    have h := hall v
    rw [LinearMap.sub_apply, Module.End.one_apply, tmul_sub, sub_eq_zero] at h
    rw [LinearMap.baseChange_tmul]
    change c ⊗ₜ[A] (ρ.ρ τ₀) v = c ⊗ₜ[A] v
    have : c ⊗ₜ[A] (ρ.ρ τ₀) v = c • ((1 : k) ⊗ₜ[A] (ρ.ρ τ₀) v) := by
      rw [smul_tmul', smul_eq_mul, mul_one]
    rw [this, h, smul_tmul', smul_eq_mul, mul_one]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

omit [IsReduced A] in

theorem exists_adapted_basis {τ₀ : Γ} (hN₀ : (ρ.ρ τ₀ - 1) * (ρ.ρ τ₀ - 1) = 0)
    (hτ₀ : ρ.residual.ρ τ₀ ≠ 1) :
    ∃ b : Module.Basis (Fin 2) A ρ.V, (ρ.ρ τ₀ - 1) (b 1) = b 0 ∧ (ρ.ρ τ₀ - 1) (b 0) = 0 := by
  obtain ⟨v₁, hv₁⟩ := exists_tmul_ne_zero ρ hτ₀
  set N₀ : Module.End A ρ.V := ρ.ρ τ₀ - 1 with hN₀def
  set w : ρ.V := N₀ v₁ with hwdef
  have hNw : N₀ w = 0 := by
    show (N₀ * N₀) v₁ = 0
    rw [hN₀, LinearMap.zero_apply]

  set f : Fin 2 → ρ.V := ![w, v₁] with hfdef
  have hf0 : f 0 = w := rfl
  have hf1 : f 1 = v₁ := rfl

  set Nk : Module.End k (k ⊗[A] ρ.V) := N₀.baseChange k with hNkdef
  have hNk_v : Nk ((1 : k) ⊗ₜ[A] v₁) = (1 : k) ⊗ₜ[A] w := by
    rw [hNkdef, LinearMap.baseChange_tmul]
  have hNk_w : Nk ((1 : k) ⊗ₜ[A] w) = 0 := by
    rw [hNkdef, LinearMap.baseChange_tmul, hNw, tmul_zero]
  have hw_ne : (1 : k) ⊗ₜ[A] w ≠ 0 := hv₁

  have hli_k : LinearIndependent k (TensorProduct.mk A k ρ.V 1 ∘ f) := by
    have hcomp : TensorProduct.mk A k ρ.V 1 ∘ f = ![(1 : k) ⊗ₜ[A] w, (1 : k) ⊗ₜ[A] v₁] := by
      ext i
      fin_cases i <;> rfl
    rw [hcomp, LinearIndependent.pair_iff]
    intro s t hst
    have h1 : t • ((1 : k) ⊗ₜ[A] w) = 0 := by
      have := congrArg Nk hst
      rwa [map_add, map_smul, map_smul, hNk_w, hNk_v, smul_zero, zero_add, map_zero] at this
    have ht : t = 0 := by
      rcases smul_eq_zero.mp h1 with h | h
      · exact h
      · exact absurd h hw_ne
    rw [ht, zero_smul, add_zero] at hst
    have hs : s = 0 := by
      rcases smul_eq_zero.mp hst with h | h
      · exact h
      · exact absurd h hw_ne
    exact ⟨hs, ht⟩

  have hrank : Fintype.card (Fin 2) = Module.finrank k (k ⊗[A] ρ.V) := by
    rw [Fintype.card_fin]
    exact ρ.residual.finrank_eq.symm
  haveI : FiniteDimensional k (k ⊗[A] ρ.V) := by
    show FiniteDimensional k ρ.residual.V
    exact FiniteDimensional.of_finrank_eq_succ ρ.residual.finrank_eq
  set bk : Module.Basis (Fin 2) k (k ⊗[A] ρ.V) :=
    basisOfLinearIndependentOfCardEqFinrank hli_k hrank with hbkdef
  have hbk : ∀ i, (1 : k) ⊗ₜ[A] f i = bk i := by
    intro i
    rw [hbkdef, coe_basisOfLinearIndependentOfCardEqFinrank]
    rfl
  have hsp : Submodule.span A (Set.range f) = ⊤ :=
    IsLocalRing.span_eq_top_of_tmul_eq_basis f bk hbk
  have hli : LinearIndependent A f := Module.IsLocalRing.linearIndependent_of_flat f hli_k
  refine ⟨Module.Basis.mk hli (by rw [hsp]), ?_, ?_⟩
  · rw [Module.Basis.mk_apply, Module.Basis.mk_apply, hf1, hf0]
  · rw [Module.Basis.mk_apply, hf0, hNw]

theorem apply_zero_eq_zero_and_repr_one_eq_zero
    (b : Module.Basis (Fin 2) A ρ.V) {N₀ N : Module.End A ρ.V}
    (h₀1 : N₀ (b 1) = b 0) (h₀0 : N₀ (b 0) = 0)
    (hNN : N * N = 0) (htr : LinearMap.trace A ρ.V (N * N₀) = 0) :
    N (b 0) = 0 ∧ b.repr (N (b 1)) 1 = 0 := by

  set α := b.repr (N (b 0)) 0 with hα
  set β := b.repr (N (b 0)) 1 with hβ
  set γ := b.repr (N (b 1)) 0 with hγ
  set δ := b.repr (N (b 1)) 1 with hδ
  have hNw : N (b 0) = α • b 0 + β • b 1 := repr_expand b _
  have hNv : N (b 1) = γ • b 0 + δ • b 1 := repr_expand b _

  have htrβ : LinearMap.trace A ρ.V (N * N₀) = β := by
    rw [LinearMap.trace_eq_matrix_trace A b, Matrix.trace_fin_two, LinearMap.toMatrix_mul,
      Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
    simp only [LinearMap.toMatrix_apply, h₀0, h₀1, map_zero, Finsupp.zero_apply,
      Module.Basis.repr_self, Finsupp.single_apply]
    simp [hβ]
  have hβ0 : β = 0 := by rw [← htrβ, htr]

  rw [hβ0, zero_smul, add_zero] at hNw
  have hα2 : α * α = 0 := by
    have h : (N * N) (b 0) = 0 := by rw [hNN, LinearMap.zero_apply]
    rw [Module.End.mul_apply, hNw, map_smul, hNw, smul_smul] at h
    have := congrArg (fun x => b.repr x 0) h
    simpa using this
  have hα0 : α = 0 := IsReduced.eq_zero α ⟨2, by rw [pow_two, hα2]⟩
  rw [hα0, zero_smul] at hNw

  have hδ2 : δ * δ = 0 := by
    have h : (N * N) (b 1) = 0 := by rw [hNN, LinearMap.zero_apply]
    rw [Module.End.mul_apply, hNv, map_add, map_smul, map_smul, hNw, hNv, smul_zero, zero_add,
      smul_add, smul_smul, smul_smul] at h
    have := congrArg (fun x => b.repr x 1) h
    simpa using this
  have hδ0 : δ = 0 := IsReduced.eq_zero δ ⟨2, by rw [pow_two, hδ2]⟩
  exact ⟨hNw, hδ0⟩

end Main

end K1G13Brick

open K1G13Brick in

theorem K1G13Brick.exists_basis
    {A : Type} [CommRing A] [IsLocalRing A] [IsReduced A]
    (ρ : GaloisRepAdic A) (q : ℕ) (hunip : ρ.IsUnipotentOnInertiaAt q)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (τ₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hτ₀ : τ₀ ∈ P.inertiaSubgroupIn ℚ)
    (hτ₀' : ρ.residual.ρ τ₀ ≠ 1) :
    ∃ b : Module.Basis (Fin 2) A ρ.V,
      (⨆ τ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρ.ρ τ - 1)) = A ∙ b 0 ∧
      (∀ τ ∈ P.inertiaSubgroupIn ℚ, ρ.ρ τ (b 0) = b 0) ∧
      (∀ σ ∈ P.decompositionSubgroup ℚ, ρ.ρ σ (b 0) ∈ A ∙ b 0) ∧
      ∃ u : A, ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ q →
        ∀ v : ρ.V, ρ.ρ σ v - u • v ∈ A ∙ b 0 := by
  have hV : Module.finrank A ρ.V = 2 := ρ.finrank_eq

  have hN₀ : (ρ.ρ τ₀ - 1) * (ρ.ρ τ₀ - 1) = 0 :=
    sub_one_mul_sub_one_eq_zero (hunip P hP τ₀ hτ₀)

  obtain ⟨b, hb1, hb0⟩ := exists_adapted_basis ρ hN₀ hτ₀'

  have hkey : ∀ τ ∈ P.inertiaSubgroupIn ℚ,
      (ρ.ρ τ - 1) (b 0) = 0 ∧ b.repr ((ρ.ρ τ - 1) (b 1)) 1 = 0 := by
    intro τ hτ
    have hcp := hunip P hP τ hτ
    have hNN : (ρ.ρ τ - 1) * (ρ.ρ τ - 1) = 0 := sub_one_mul_sub_one_eq_zero hcp
    obtain ⟨htrτ, -⟩ := trace_det_of_charpoly hV hcp
    obtain ⟨htr₀, -⟩ := trace_det_of_charpoly hV (hunip P hP τ₀ hτ₀)
    obtain ⟨htrp, -⟩ := trace_det_of_charpoly hV
      (hunip P hP (τ * τ₀) (Subgroup.mul_mem _ hτ hτ₀))
    have htr : LinearMap.trace A ρ.V ((ρ.ρ τ - 1) * (ρ.ρ τ₀ - 1)) = 0 := by
      have hexp : (ρ.ρ τ - 1) * (ρ.ρ τ₀ - 1) = ρ.ρ (τ * τ₀) - ρ.ρ τ - ρ.ρ τ₀ + 1 := by
        rw [map_mul]; noncomm_ring
      rw [hexp, map_add, map_sub, map_sub, htrp, htrτ, htr₀, trace_one hV]
      ring
    exact apply_zero_eq_zero_and_repr_one_eq_zero ρ b hb1 hb0 hNN htr

  have hfix : ∀ τ ∈ P.inertiaSubgroupIn ℚ, ρ.ρ τ (b 0) = b 0 := by
    intro τ hτ
    have h := (hkey τ hτ).1
    rwa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h
  have hrange : ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ.V, (ρ.ρ τ - 1) v ∈ A ∙ b 0 := by
    intro τ hτ v
    obtain ⟨h0, h1⟩ := hkey τ hτ
    rw [repr_expand b v, map_add, map_smul, map_smul, h0, smul_zero, zero_add]
    refine Submodule.smul_mem _ _ ?_
    exact (mem_span_iff_repr_one_eq_zero b _).mpr h1
  have hrange' : ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ τ v - v ∈ A ∙ b 0 := by
    intro τ hτ v
    simpa [LinearMap.sub_apply] using hrange τ hτ v

  have hsup : (⨆ τ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρ.ρ τ - 1)) = A ∙ b 0 := by
    apply le_antisymm
    · refine iSup₂_le fun τ hτ => ?_
      rintro _ ⟨v, rfl⟩
      exact hrange τ hτ v
    · rw [Submodule.span_singleton_le_iff_mem]
      have hle : LinearMap.range (ρ.ρ τ₀ - 1) ≤
          ⨆ τ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρ.ρ τ - 1) :=
        le_iSup₂ (f := fun τ _ => LinearMap.range (ρ.ρ τ - 1)) τ₀ hτ₀
      exact hle ⟨b 1, hb1⟩

  have hstab : ∀ σ ∈ P.decompositionSubgroup ℚ, ρ.ρ σ (b 0) ∈ A ∙ b 0 := by
    intro σ hσ
    have hconj := conj_mem_inertiaSubgroupIn P hσ hτ₀
    have hcalc : ρ.ρ σ (b 0) = (ρ.ρ (σ * τ₀ * σ⁻¹) - 1) (ρ.ρ σ (b 1)) := by
      rw [← hb1, LinearMap.sub_apply, LinearMap.sub_apply, Module.End.one_apply,
        Module.End.one_apply, map_sub, ← Module.End.mul_apply, ← map_mul,
        ← Module.End.mul_apply (ρ.ρ (σ * τ₀ * σ⁻¹)), ← map_mul]
      congr 2
      group
    rw [hcalc]
    exact hrange _ hconj _
  have hstab' : ∀ σ ∈ P.decompositionSubgroup ℚ, ∀ x ∈ A ∙ b 0, ρ.ρ σ x ∈ A ∙ b 0 := by
    intro σ hσ x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [map_smul]
    exact Submodule.smul_mem _ _ (hstab σ hσ)
  refine ⟨b, hsup, hfix, hstab, ?_⟩

  by_cases hex : ∃ σ₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ₀ q
  · obtain ⟨σ₀, hσ₀⟩ := hex
    refine ⟨b.repr (ρ.ρ σ₀ (b 1)) 1, fun σ hσ v => ?_⟩
    set u := b.repr (ρ.ρ σ₀ (b 1)) 1 with hu
    have hD₀ := hσ₀.mem_decompositionSubgroup

    have hι : σ₀⁻¹ * σ ∈ P.inertiaSubgroupIn ℚ :=
      inv_mul_mem_inertiaSubgroupIn_of_isFrobeniusAt P hσ₀ hσ
    have hdiff : ρ.ρ σ v - ρ.ρ σ₀ v ∈ A ∙ b 0 := by
      have h1 : ρ.ρ σ v = ρ.ρ σ₀ (ρ.ρ (σ₀⁻¹ * σ) v) := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
      rw [h1, ← map_sub]
      exact hstab' σ₀ hD₀ _ (hrange' _ hι v)

    have hσ₀v : ρ.ρ σ₀ v - u • v ∈ A ∙ b 0 := by
      have hb1exp : ρ.ρ σ₀ (b 1) = b.repr (ρ.ρ σ₀ (b 1)) 0 • b 0 + u • b 1 := repr_expand b _
      rw [repr_expand b v, map_add, map_smul, map_smul, smul_add, hb1exp]
      have hmem0 : b.repr v 0 • ρ.ρ σ₀ (b 0) - u • b.repr v 0 • b 0 ∈ A ∙ b 0 :=
        Submodule.sub_mem _ (Submodule.smul_mem _ _ (hstab σ₀ hD₀))
          (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
      have hmem1 : b.repr v 1 • (b.repr (ρ.ρ σ₀ (b 1)) 0 • b 0 + u • b 1) -
          u • b.repr v 1 • b 1 ∈ A ∙ b 0 := by
        rw [smul_add, smul_smul, smul_smul, smul_smul, mul_comm (b.repr v 1) u, add_sub_cancel_right]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      convert Submodule.add_mem _ hmem0 hmem1 using 1
      abel
    have := Submodule.add_mem _ hdiff hσ₀v
    convert this using 1
    abel
  · exact ⟨0, fun σ hσ => absurd ⟨σ, hσ⟩ hex⟩

theorem solution
    {A : Type} [CommRing A] [IsLocalRing A] [IsReduced A]
    (ρ : GaloisRepAdic A) (q : ℕ) (hunip : ρ.IsUnipotentOnInertiaAt q)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (τ₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hτ₀ : τ₀ ∈ P.inertiaSubgroupIn ℚ)
    (hτ₀' : ρ.residual.ρ τ₀ ≠ 1) :
    ∃ (L : Submodule A ρ.V) (u : A),
      (∃ b : Module.Basis (Fin 2) A ρ.V, L = A ∙ b 0) ∧
      (⨆ τ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρ.ρ τ - 1)) = L ∧
      (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L, ρ.ρ σ v ∈ L) ∧
      (∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ v ∈ L, ρ.ρ τ v = v) ∧
      (∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ τ v - v ∈ L) ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ q →
        ∀ v : ρ.V, ρ.ρ σ v - u • v ∈ L) := by
  obtain ⟨b, hsup, hfix, hstab, u, hu⟩ := K1G13Brick.exists_basis ρ q hunip P hP τ₀ hτ₀ hτ₀'
  refine ⟨A ∙ b 0, u, ⟨b, rfl⟩, hsup, ?_, ?_, ?_, hu⟩
  · intro σ hσ x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [map_smul]
    exact Submodule.smul_mem _ _ (hstab σ hσ)
  · intro τ hτ x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [map_smul, hfix τ hτ]
  · intro τ hτ v
    rw [← hsup]
    have hle : LinearMap.range (ρ.ρ τ - 1) ≤
        ⨆ τ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρ.ρ τ - 1) :=
      le_iSup₂ (f := fun τ _ => LinearMap.range (ρ.ρ τ - 1)) τ hτ
    exact hle ⟨v, by simp [LinearMap.sub_apply]⟩

end S_GaloisRepAdic_exists_stableLine_frobenius_sub_smul_mem_of_isUnipotentOnInertiaAt_of_residual_ne_one
end P2MW
export P2MW.S_GaloisRepAdic_exists_stableLine_frobenius_sub_smul_mem_of_isUnipotentOnInertiaAt_of_residual_ne_one (solution)
