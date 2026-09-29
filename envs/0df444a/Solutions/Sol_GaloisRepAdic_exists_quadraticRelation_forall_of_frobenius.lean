-- Prove2me | solution 1 for GaloisRepAdic.exists_quadraticRelation_forall_of_frobenius
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/2f7fcc56-7c6b-577a-8506-6fb086f9a717

import Mathlib
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FieldTheory_RatAlgClosureGalois
import Theorems.Thm_PadicInt_nonempty_ringHom_of_isAdicComplete_of_natCast_mem
import Theorems.Thm_AlgebraicClosure_exists_monoidHom_zmod_units_frobenius_eq_unitOfCoprime
import Theorems.Thm_AlgebraicClosure_exists_intermediateField_toZModPow_cyclotomicCharacter_eq_one
import Theorems.Thm_IsLocalRing_exists_maximalIdeal_pow_le_span_natCast_pow_of_module_finite
import Theorems.Thm_GaloisRepAdic_exists_intermediateField_trace_mul_sub_trace_mem
import Theorems.Thm_Representation_quadraticRelation_apply_mem_of_conj_mul_of_eq_zero
import Theorems.Thm_FrobeniusDensity_exists_isFrobeniusAt_conj_mem_of_le_ker
import Theorems.Thm_ValuationSubring_coe_cyclotomicCharacter_eq_natCast_of_isFrobeniusAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_exists_quadraticRelation_forall_of_frobenius
p2m_attr_erase "instance" "FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false

open IsLocalRing

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    {R : Type} [CommRing R] [IsLocalRing R] [Algebra 𝒪 R] [Module.Finite 𝒪 R]
    (hl : IsLocalHom (algebraMap 𝒪 R))
    (ρ : GaloisRepAdic R)
    {Y : Type} [AddCommGroup Y] [Module R Y] [Module 𝒪 Y] [IsScalarTower 𝒪 R Y] [Module.Finite 𝒪 Y]
    (ρY : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End R Y)
    (hcont : ∀ n : ℕ, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ F, σ x = x) →
        ∀ y : Y, ρY σ y - y ∈ (Ideal.span {(p : R)} ^ n • (⊤ : Submodule R Y)))
    (L : ℕ) [NeZero L] (D : (ZMod L)ˣ →* Module.End R Y)
    (hD : ∀ (u : (ZMod L)ˣ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), D u * ρY σ = ρY σ * D u)
    (S₀ : Finset ℕ)
    (hES : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S₀ → ∀ (hℓL : ¬ ℓ ∣ L), ℓ ≠ p →
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          ρY σ * ρY σ - (ρ.trace σ) • ρY σ
            + (ℓ : R) • D (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓL)) = 0) :
    ∃ (c : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Rˣ)
      (χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod L)ˣ),
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        ρY σ * ρY σ - (ρ.trace σ) • ρY σ + ((c σ : Rˣ) : R) • D (χ σ) = 0 := by
  classical
  haveI : Fact p.Prime := inferInstance

  obtain ⟨φ⟩ := PadicInt.nonempty_ringHom_of_isAdicComplete_of_natCast_mem 𝒪 (maximalIdeal 𝒪) p hp𝒪
  let ι : ℤ_[p] →+* R := (algebraMap 𝒪 R).comp φ
  let εA : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* ℤ_[p]ˣ :=
    { toFun := fun σ => cyclotomicCharacter (AlgebraicClosure ℚ) p σ.toRingEquiv
      map_one' := map_one _
      map_mul' := fun a b => by rw [← map_mul]; rfl }
  let cE : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Rˣ := (Units.map (ι : ℤ_[p] →* R)).comp εA
  have hcE : ∀ σ, ((cE σ : Rˣ) : R) = ι ((cyclotomicCharacter (AlgebraicClosure ℚ) p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) := fun _ => rfl
  obtain ⟨χ, Fχ, hFχ, hχ1, hχfrob⟩ := AlgebraicClosure.exists_monoidHom_zmod_units_frobenius_eq_unitOfCoprime L
  refine ⟨cE, χ, fun σ => ?_⟩

  suffices hmod : ∀ (n : ℕ) (y : Y), (ρY σ * ρY σ - (ρ.trace σ) • ρY σ + ((cE σ : Rˣ) : R) • D (χ σ)) y ∈
      (Ideal.span {(p : R)} ^ n • (⊤ : Submodule R Y)) by
    apply LinearMap.ext
    intro y
    rw [LinearMap.zero_apply]
    have hI : (Ideal.span {(p : 𝒪)} : Ideal 𝒪) ≠ ⊤ := fun h =>
      (maximalIdeal.isMaximal 𝒪).ne_top (top_le_iff.mp (h ▸ (Ideal.span_singleton_le_iff_mem _).2 hp𝒪))
    have hK := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := Y) (Ideal.span {(p : 𝒪)}) hI
    have hmem : (ρY σ * ρY σ - (ρ.trace σ) • ρY σ + ((cE σ : Rˣ) : R) • D (χ σ)) y ∈
        ⨅ i : ℕ, (Ideal.span {(p : 𝒪)} ^ i • (⊤ : Submodule 𝒪 Y)) := by
      rw [Submodule.mem_iInf]
      intro i
      have h := hmod i y
      rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul] at h
      rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul]
      obtain ⟨z, -, hz⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h
      refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨z, Submodule.mem_top, ?_⟩
      rw [← hz, show ((p : R)) ^ i = algebraMap 𝒪 R ((p : 𝒪) ^ i) by rw [map_pow, map_natCast], algebraMap_smul]
    rw [hK] at hmem
    exact (Submodule.mem_bot 𝒪).1 hmem
  intro n

  obtain ⟨m, hm⟩ := IsLocalRing.exists_maximalIdeal_pow_le_span_natCast_pow_of_module_finite p hp𝒪 hl n
  obtain ⟨Ft, hFt, htr⟩ := GaloisRepAdic.exists_intermediateField_trace_mul_sub_trace_mem ρ (Ideal.span {(p : R)} ^ n) ⟨m, hm⟩
  obtain ⟨FY, hFY, hY⟩ := hcont n
  obtain ⟨Fε, hFε, hε⟩ := AlgebraicClosure.exists_intermediateField_toZModPow_cyclotomicCharacter_eq_one p n
  haveI := hFt; haveI := hFY; haveI := hFε; haveI := hFχ
  let F₀ : IntermediateField ℚ (AlgebraicClosure ℚ) := Ft ⊔ FY ⊔ Fε ⊔ Fχ
  haveI : FiniteDimensional ℚ ↥F₀ := IntermediateField.finiteDimensional_sup _ _
  let F : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.normalClosure ℚ F₀ (AlgebraicClosure ℚ)
  haveI : IsGalois ℚ ↥F := IsGalois.normalClosure ℚ ↥F₀ (AlgebraicClosure ℚ)
  haveI : NumberField ↥F := NumberField.mk
  have hle : F₀ ≤ F := IntermediateField.le_normalClosure F₀
  have hfixF : ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, τ ∈ F.fixingSubgroup →
      (∀ x ∈ Ft, τ x = x) ∧ (∀ x ∈ FY, τ x = x) ∧ (∀ x ∈ Fε, τ x = x) ∧ (∀ x ∈ Fχ, τ x = x) := by
    intro τ hτ
    rw [IntermediateField.mem_fixingSubgroup_iff] at hτ
    have h0 : ∀ x ∈ F₀, τ x = x := fun x hx => hτ x (hle hx)
    have l1 : Ft ≤ F₀ := le_sup_left.trans (le_sup_left.trans le_sup_left)
    have l2 : FY ≤ F₀ := le_sup_right.trans (le_sup_left.trans le_sup_left)
    have l3 : Fε ≤ F₀ := le_sup_right.trans le_sup_left
    have l4 : Fχ ≤ F₀ := le_sup_right
    exact ⟨fun x hx => h0 x (l1 hx), fun x hx => h0 x (l2 hx), fun x hx => h0 x (l3 hx), fun x hx => h0 x (l4 hx)⟩

  have hN : ∀ (g s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), s ∈ F.fixingSubgroup → g⁻¹ * s * g ∈ F.fixingSubgroup := by
    intro g s hs
    rw [IntermediateField.mem_fixingSubgroup_iff] at hs ⊢
    intro x hx
    have hx' : g x ∈ F := (IntermediateField.normal_iff_forall_map_le'.1 inferInstance g) ⟨x, hx, rfl⟩
    show g⁻¹ (s (g x)) = x
    rw [hs _ hx', ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]

  haveI : NeZero L := inferInstance
  let Sbad : Finset ℕ := S₀ ∪ {p} ∪ L.primeFactors
  obtain ⟨ℓ, A, τ, g, hℓ, hℓS, hA, hτ, hk⟩ :=
    FrobeniusDensity.exists_isFrobeniusAt_conj_mem_of_le_ker ↥F (H := F.fixingSubgroup)
      (IntermediateField.restrictNormalHom_ker F).le Sbad σ
  have hℓS₀ : ℓ ∉ S₀ := fun h => hℓS (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have hℓp : ℓ ≠ p := fun h => hℓS (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.2 h)))
  have hℓL : ¬ ℓ ∣ L := fun h => hℓS (Finset.mem_union_right _ (Nat.mem_primeFactors.2 ⟨hℓ, h, NeZero.ne L⟩))

  have hτrel : ρY τ * ρY τ - (ρ.trace τ) • ρY τ + ((cE τ : Rˣ) : R) • D (χ τ) = 0 := by
    have h := hES ℓ hℓ hℓS₀ hℓL hℓp A hA τ hτ
    have hc : ((cE τ : Rˣ) : R) = (ℓ : R) := by
      rw [hcE, ValuationSubring.coe_cyclotomicCharacter_eq_natCast_of_isFrobeniusAt (p := p) hℓ hℓp A hA τ hτ, map_natCast]
    rw [hc, hχfrob ℓ hℓ hℓL A hA τ hτ, ← h]

  set N : Submodule R Y := Ideal.span {(p : R)} ^ n • ⊤ with hNdef
  have hNlin : ∀ (f : Module.End R Y), ∀ y ∈ N, f y ∈ N := by
    intro f y hy
    rw [hNdef] at hy ⊢
    have : Submodule.map f (Ideal.span {(p : R)} ^ n • ⊤) ≤ Ideal.span {(p : R)} ^ n • ⊤ := by
      rw [Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top
    exact this ⟨y, hy, rfl⟩
  have hk' : (g * τ * g⁻¹)⁻¹ * σ ∈ F.fixingSubgroup := by
    have h1 : (g * τ * g⁻¹ * σ⁻¹)⁻¹ ∈ F.fixingSubgroup := F.fixingSubgroup.inv_mem hk
    have h2 := hN (g * τ * g⁻¹) _ h1
    have : (g * τ * g⁻¹)⁻¹ * (g * τ * g⁻¹ * σ⁻¹)⁻¹ * (g * τ * g⁻¹) = (g * τ * g⁻¹)⁻¹ * σ := by group
    rwa [this] at h2
  have hσeq : σ = g * τ * g⁻¹ * ((g * τ * g⁻¹)⁻¹ * σ) := by group
  intro y
  rw [hσeq]
  refine Representation.quadraticRelation_apply_mem_of_conj_mul_of_eq_zero ρY ρ.trace cE χ D
    (fun a b => ?_) hD N (fun f y hy => hNlin _ y hy) (fun u y hy => hNlin _ y hy) F.fixingSubgroup
    (fun a h hh y => ?_) (fun a h hh y => ?_) (fun a h hh y => ?_) (fun a h hh => ?_) τ hτrel g _ hk' y
  ·
    show LinearMap.trace R ρ.V (ρ.ρ (a * b * a⁻¹)) = LinearMap.trace R ρ.V (ρ.ρ b)
    rw [map_mul ρ.ρ, map_mul ρ.ρ, LinearMap.trace_mul_comm R (ρ.ρ a * ρ.ρ b) (ρ.ρ a⁻¹), ← mul_assoc, ← map_mul ρ.ρ,
      inv_mul_cancel, map_one, one_mul]
  ·
    have := hY h (hfixF h hh).2.1 y
    rw [map_mul, Module.End.mul_apply, ← map_sub]
    exact hNlin _ _ this
  ·
    rw [hNdef]
    exact Submodule.smul_mem_smul (htr a h (hfixF h hh).1) Submodule.mem_top
  ·
    have h1 := hε h (hfixF h hh).2.2.1
    have h2 : ((cyclotomicCharacter (AlgebraicClosure ℚ) p h.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) - 1 ∈ Ideal.span {(p : ℤ_[p])} ^ n := by
      rw [Ideal.span_singleton_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, h1, map_one, sub_self]
    have h3 : ((cE (a * h) : Rˣ) : R) - ((cE a : Rˣ) : R) = ((cE a : Rˣ) : R) * (ι (((cyclotomicCharacter (AlgebraicClosure ℚ) p h.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p])) - 1) := by
      rw [map_mul, Units.val_mul, hcE h, mul_sub, mul_one]
    rw [h3, mul_smul, hNdef]
    refine hNlin (((cE a : Rˣ) : R) • LinearMap.id) _ (Submodule.smul_mem_smul ?_ Submodule.mem_top)
    have : ι (((cyclotomicCharacter (AlgebraicClosure ℚ) p h.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p])) - 1 ∈ Ideal.map ι (Ideal.span {(p : ℤ_[p])} ^ n) := by
      rw [← map_one ι, ← map_sub]
      exact Ideal.mem_map_of_mem ι h2
    rwa [Ideal.map_pow, Ideal.map_span, Set.image_singleton, map_natCast] at this
  ·
    rw [map_mul, hχ1 h (hfixF h hh).2.2.2, mul_one]

end S_GaloisRepAdic_exists_quadraticRelation_forall_of_frobenius
end P2MW
export P2MW.S_GaloisRepAdic_exists_quadraticRelation_forall_of_frobenius (solution)
