-- Prove2me | solution 1 for FrobeniusDensity.ncard_degreeOne_primesOver_under
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/61dec792-5ef6-58bd-894a-134e134603cf

import Theorems.Thm_FrobeniusDensity_stabilizer_eq_zpowers_arithFrobAt
import Definitions.Def_FrobeniusDensity_BadPrimes
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Fixed
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Tactic.Group
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FrobeniusDensity_ncard_degreeOne_primesOver_under

set_option autoImplicit false

p2m_open "NumberField Ideal NumberField.Ideal"
open scoped Pointwise
attribute [local instance 1001] NumberField.RingOfIntegers.instMulSemiringAction
attribute [local instance] Ideal.Quotient.field

namespace FrobeniusDensity
p2m_export "FrobeniusDensity" "stabilizer_eq_zpowers_arithFrobAt ratPrimeIdeal ratPrimeIdeal_ne_bot finite_quotient_of_ne_bot ne_bot_of_liesOver_ratPrimeIdeal card_quotient_under_int"
p2m_open "FrobeniusDensity"

variable {L : Type*} [Field L] [NumberField L]

private theorem inertia_smul_eq_bot {Q : Ideal (𝓞 L)}
    (hQ : Q.inertia (L ≃ₐ[ℚ] L) = ⊥) (g : L ≃ₐ[ℚ] L) :
    (g • Q).inertia (L ≃ₐ[ℚ] L) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall] at hQ ⊢
  intro σ hσ
  have h : g⁻¹ * σ * g ∈ Q.inertia (L ≃ₐ[ℚ] L) := by
    intro x
    have hx := hσ (g • x)
    rw [Submodule.mem_toAddSubgroup, Ideal.mem_pointwise_smul_iff_inv_smul_mem, smul_sub] at hx
    simpa [Submodule.mem_toAddSubgroup, mul_smul] using hx
  have h1 := hQ _ h
  rw [show σ = g * (g⁻¹ * σ * g) * g⁻¹ by group, h1]
  group

variable {H : Subgroup (L ≃ₐ[ℚ] L)} {E : IntermediateField ℚ L} [IsGaloisGroup H E L]

private theorem under_smul_of_mem {σ : L ≃ₐ[ℚ] L} (hσ : σ ∈ H) (Q : Ideal (𝓞 L)) :
    (σ • Q).under (𝓞 E) = Q.under (𝓞 E) := by
  rw [show σ • Q = (⟨σ, hσ⟩ : H) • Q from rfl]
  exact Ideal.under_smul (𝓞 E) Q (⟨σ, hσ⟩ : H)

scoped instance : SMulCommClass H (𝓞 E) (𝓞 L) := IsGaloisGroup.commutes

private theorem isArithFrobAt_coe_of_card_eq {Q : Ideal (𝓞 L)} {τ : H}
    (h : IsArithFrobAt (𝓞 E) τ Q)
    (hcard : Nat.card ((𝓞 E) ⧸ Q.under (𝓞 E)) = Nat.card (ℤ ⧸ Q.under ℤ)) :
    IsArithFrobAt ℤ (τ : L ≃ₐ[ℚ] L) Q := by
  intro x
  have hx := h x
  rw [hcard] at hx
  exact hx

private theorem exists_isArithFrobAt_mem {Q : Ideal (𝓞 L)} [Q.IsPrime] (hQ : Q ≠ ⊥)
    (hcard : Nat.card ((𝓞 E) ⧸ Q.under (𝓞 E)) = Nat.card (ℤ ⧸ Q.under ℤ)) :
    ∃ σ : L ≃ₐ[ℚ] L, σ ∈ H ∧ IsArithFrobAt ℤ σ Q := by
  have : Finite ((𝓞 L) ⧸ Q) := finite_quotient_of_ne_bot hQ
  obtain ⟨τ, hτ⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 E) H Q
  exact ⟨(τ : L ≃ₐ[ℚ] L), τ.2, isArithFrobAt_coe_of_card_eq hτ hcard⟩

private theorem mem_of_isArithFrobAt_of_card_eq {Q : Ideal (𝓞 L)} [Q.IsPrime] (hQ : Q ≠ ⊥)
    {σ : L ≃ₐ[ℚ] L} (hσ : IsArithFrobAt ℤ σ Q)
    (hcard : Nat.card ((𝓞 E) ⧸ Q.under (𝓞 E)) = Nat.card (ℤ ⧸ Q.under ℤ))
    (hinertia : Q.inertia (L ≃ₐ[ℚ] L) ≤ H) :
    σ ∈ H := by
  obtain ⟨τ, hτH, hτ⟩ := exists_isArithFrobAt_mem (H := H) (E := E) hQ hcard
  have hmem : σ * τ⁻¹ ∈ Q.inertia (L ≃ₐ[ℚ] L) := hσ.mul_inv_mem_inertia hτ
  simpa using mul_mem (hinertia hmem) hτH

variable {ℓ : ℕ} [IsGalois ℚ L]

private theorem le_card_quotient_under (hℓ : ℓ.Prime) (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Q.LiesOver (ratPrimeIdeal ℓ)] :
    ℓ ≤ Nat.card ((𝓞 E) ⧸ Q.under (𝓞 E)) := by
  haveI h𝔮 : (Q.under (𝓞 E)).LiesOver (ratPrimeIdeal ℓ) := Ideal.LiesOver.tower_bot Q _ _
  have h𝔮bot : Q.under (𝓞 E) ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot (ratPrimeIdeal_ne_bot hℓ) _
  have : Finite ((𝓞 E) ⧸ Q.under (𝓞 E)) := finite_quotient_of_ne_bot h𝔮bot
  calc ℓ = Nat.card (ℤ ⧸ (Q.under (𝓞 E)).under ℤ) :=
        (card_quotient_under_int (ℓ := ℓ) (Q.under (𝓞 E))).symm
    _ ≤ Nat.card ((𝓞 E) ⧸ Q.under (𝓞 E)) :=
        Nat.card_le_card_of_injective _ (FaithfulSMul.algebraMap_injective _ _)

open Polynomial in
private theorem card_le_of_forall_pow_eq {K : Type*} [CommRing K] [IsDomain K] [Finite K]
    {n : ℕ} (hn : 1 < n) (h : ∀ x : K, x ^ n = x) : Nat.card K ≤ n := by
  cases nonempty_fintype K
  have hdeg : (X ^ n - X : K[X]).natDegree = n := by
    rw [natDegree_sub_eq_left_of_natDegree_lt (by rw [natDegree_X, natDegree_X_pow]; exact hn),
      natDegree_X_pow]
  have hne : (X ^ n - X : K[X]) ≠ 0 := ne_zero_of_natDegree_gt (n := 0) (by omega)
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ, ← hdeg]
  refine card_le_degree_of_subset_roots fun x _ ↦ ?_
  rw [mem_roots hne]
  simp [Polynomial.IsRoot, h x]

private theorem exists_isArithFrobAt' {Q : Ideal (𝓞 L)} [Q.IsPrime] (hQ : Q ≠ ⊥) :
    ∃ σ : L ≃ₐ[ℚ] L, IsArithFrobAt ℤ σ Q :=
  have : Finite (𝓞 L ⧸ Q) := finite_quotient_of_ne_bot hQ
  IsArithFrobAt.exists_of_isInvariant ℤ (L ≃ₐ[ℚ] L) Q

private theorem card_under_eq_of_stabilizer_le (hℓ : ℓ.Prime) (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Q.LiesOver (ratPrimeIdeal ℓ)]
    (hstab : MulAction.stabilizer (L ≃ₐ[ℚ] L) Q ≤ H) :
    Nat.card ((𝓞 E) ⧸ Q.under (𝓞 E)) = ℓ := by
  refine le_antisymm ?_ (le_card_quotient_under hℓ Q)
  have hQbot : Q ≠ ⊥ := ne_bot_of_liesOver_ratPrimeIdeal hℓ
  obtain ⟨σ, hσ⟩ := exists_isArithFrobAt' (L := L) hQbot
  have hσH : σ ∈ H := hstab hσ.mem_stabilizer
  haveI h𝔮 : (Q.under (𝓞 E)).LiesOver (ratPrimeIdeal ℓ) := Ideal.LiesOver.tower_bot Q _ _
  have h𝔮bot : Q.under (𝓞 E) ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot (ratPrimeIdeal_ne_bot hℓ) _
  have : Finite ((𝓞 E) ⧸ Q.under (𝓞 E)) := finite_quotient_of_ne_bot h𝔮bot
  have hpow : ∀ y : (𝓞 E) ⧸ Q.under (𝓞 E), y ^ ℓ = y := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_pow, eq_comm, Ideal.Quotient.eq, Ideal.mem_comap]
    have hfix : (MulSemiringAction.toAlgHom ℤ (𝓞 L) σ) (algebraMap (𝓞 E) (𝓞 L) x)
        = algebraMap (𝓞 E) (𝓞 L) x := smul_algebraMap (⟨σ, hσH⟩ : H) x
    have hcong := hσ (algebraMap (𝓞 E) (𝓞 L) x)
    rw [card_quotient_under_int (ℓ := ℓ) Q, hfix] at hcong
    simpa using hcong
  exact card_le_of_forall_pow_eq hℓ.one_lt hpow

private theorem stabilizer_le_of_card_under_eq (hℓ : ℓ.Prime) (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Q.LiesOver (ratPrimeIdeal ℓ)] (hinertia : Q.inertia (L ≃ₐ[ℚ] L) = ⊥)
    (hdeg : Nat.card ((𝓞 E) ⧸ Q.under (𝓞 E)) = ℓ) :
    MulAction.stabilizer (L ≃ₐ[ℚ] L) Q ≤ H := by
  have hQbot : Q ≠ ⊥ := ne_bot_of_liesOver_ratPrimeIdeal hℓ
  haveI : Finite ((𝓞 L) ⧸ Q) := finite_quotient_of_ne_bot hQbot
  rw [stabilizer_eq_zpowers_arithFrobAt hℓ Q hinertia, Subgroup.zpowers_le]
  refine mem_of_isArithFrobAt_of_card_eq (E := E) hQbot
    (IsArithFrobAt.arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q) ?_ (hinertia ▸ bot_le)
  rw [hdeg, card_quotient_under_int (ℓ := ℓ) Q]

variable (E) in
private def restrictPrime (Q₀ : Ideal (𝓞 L)) (x : (L ≃ₐ[ℚ] L) ⧸ H) : Ideal (𝓞 E) :=
  Quotient.liftOn' x (fun g ↦ (g⁻¹ • Q₀).under (𝓞 E)) fun g₁ g₂ hg ↦ by
    have h : g₁⁻¹ * g₂ ∈ H := QuotientGroup.leftRel_apply.mp hg
    show (g₁⁻¹ • Q₀).under (𝓞 E) = (g₂⁻¹ • Q₀).under (𝓞 E)
    rw [show g₂⁻¹ = (g₁⁻¹ * g₂)⁻¹ * g₁⁻¹ by group, mul_smul]
    exact (under_smul_of_mem (inv_mem h) _).symm

private theorem restrictPrime_mk (Q₀ : Ideal (𝓞 L)) (g : L ≃ₐ[ℚ] L) :
    restrictPrime E Q₀ (g : (L ≃ₐ[ℚ] L) ⧸ H) = (g⁻¹ • Q₀).under (𝓞 E) := rfl

private theorem mem_stabilizer_inv_smul_iff (Q₀ : Ideal (𝓞 L)) (g σ : L ≃ₐ[ℚ] L) :
    σ ∈ MulAction.stabilizer (L ≃ₐ[ℚ] L) (g⁻¹ • Q₀)
      ↔ g * σ * g⁻¹ ∈ MulAction.stabilizer (L ≃ₐ[ℚ] L) Q₀ := by
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj, Subgroup.mem_map_equiv,
    MulAut.conj_symm_apply]
  group

private theorem forall_smul_eq_iff_stabilizer_le (Q₀ : Ideal (𝓞 L)) (g : L ≃ₐ[ℚ] L) :
    (∀ d ∈ MulAction.stabilizer (L ≃ₐ[ℚ] L) Q₀, d • (g : (L ≃ₐ[ℚ] L) ⧸ H) = g)
      ↔ MulAction.stabilizer (L ≃ₐ[ℚ] L) (g⁻¹ • Q₀) ≤ H := by
  constructor
  · intro hfix σ hσ
    have hd : g * σ * g⁻¹ ∈ MulAction.stabilizer (L ≃ₐ[ℚ] L) Q₀ :=
      (mem_stabilizer_inv_smul_iff Q₀ g σ).mp hσ
    have h1 := hfix _ hd
    rw [MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq,
      show (g * σ * g⁻¹ * g)⁻¹ * g = σ⁻¹ by group] at h1
    simpa using h1
  · intro hle d hd
    rw [MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq,
      show (d * g)⁻¹ * g = g⁻¹ * d⁻¹ * g by group]
    refine hle ((mem_stabilizer_inv_smul_iff Q₀ g _).mpr ?_)
    rw [show g * (g⁻¹ * d⁻¹ * g) * g⁻¹ = d⁻¹ by group]
    exact inv_mem hd

private theorem exists_mem_smul_eq_of_under_eq (Q Q' : Ideal (𝓞 L)) [Q.IsPrime] [Q'.IsPrime]
    (h : Q.under (𝓞 E) = Q'.under (𝓞 E)) :
    ∃ σ ∈ H, σ • Q = Q' := by
  haveI : Q'.LiesOver (Q.under (𝓞 E)) := ⟨h⟩
  obtain ⟨τ, hτ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Q.under (𝓞 E)) Q Q' H
  exact ⟨(τ : L ≃ₐ[ℚ] L), τ.2, hτ⟩

end FrobeniusDensity
p2m_reactivate "P2MW.S_FrobeniusDensity_ncard_degreeOne_primesOver_under.FrobeniusDensity"

p2m_open "FrobeniusDensity P2MW.S_FrobeniusDensity_ncard_degreeOne_primesOver_under.FrobeniusDensity"

theorem solution
    {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]
    {H : Subgroup (L ≃ₐ[ℚ] L)} {E : IntermediateField ℚ L} [IsGaloisGroup H E L]
    {ℓ : ℕ} (hℓ : ℓ.Prime) (Q₀ : Ideal (𝓞 L)) [Q₀.IsPrime]
    [Q₀.LiesOver (FrobeniusDensity.ratPrimeIdeal ℓ)] (hinertia : Q₀.inertia (L ≃ₐ[ℚ] L) = ⊥) :
    {𝔮 ∈ (FrobeniusDensity.ratPrimeIdeal ℓ).primesOver (𝓞 E) |
      Nat.card ((𝓞 E) ⧸ 𝔮) = ℓ}.ncard
      = {x : (L ≃ₐ[ℚ] L) ⧸ H |
          ∀ d ∈ MulAction.stabilizer (L ≃ₐ[ℚ] L) Q₀, d • x = x}.ncard := by
  set S : Set ((L ≃ₐ[ℚ] L) ⧸ H) :=
    {x | ∀ d ∈ MulAction.stabilizer (L ≃ₐ[ℚ] L) Q₀, d • x = x} with hS
  set T : Set (Ideal (𝓞 E)) :=
    {𝔮 ∈ (ratPrimeIdeal ℓ).primesOver (𝓞 E) | Nat.card ((𝓞 E) ⧸ 𝔮) = ℓ} with hT
  have hinj : Set.InjOn (restrictPrime E Q₀) S := by
    intro x hx y hy hxy
    obtain ⟨g₁, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨g₂, rfl⟩ := QuotientGroup.mk_surjective y
    rw [restrictPrime_mk, restrictPrime_mk] at hxy
    obtain ⟨τ, hτH, hτ⟩ := exists_mem_smul_eq_of_under_eq (H := H) (g₁⁻¹ • Q₀) (g₂⁻¹ • Q₀) hxy
    have hd : g₂ * τ * g₁⁻¹ ∈ MulAction.stabilizer (L ≃ₐ[ℚ] L) Q₀ := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, hτ, smul_inv_smul]
    have hfix := hx _ hd
    rw [MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq] at hfix
    have h2 : τ⁻¹ * g₂⁻¹ * g₁ ∈ H := by
      rw [show τ⁻¹ * g₂⁻¹ * g₁ = (g₂ * τ * g₁⁻¹ * g₁)⁻¹ * g₁ by group]
      exact hfix
    have h3 : g₂⁻¹ * g₁ ∈ H := by
      rw [show g₂⁻¹ * g₁ = τ * (τ⁻¹ * g₂⁻¹ * g₁) by group]
      exact mul_mem hτH h2
    rw [QuotientGroup.eq, show g₁⁻¹ * g₂ = (g₂⁻¹ * g₁)⁻¹ by group]
    exact inv_mem h3
  have himage : restrictPrime E Q₀ '' S = T := by
    ext 𝔮
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
      replace hx : MulAction.stabilizer (L ≃ₐ[ℚ] L) (g⁻¹ • Q₀) ≤ H :=
        (forall_smul_eq_iff_stabilizer_le Q₀ g).mp hx
      rw [restrictPrime_mk]
      refine ⟨⟨inferInstance, Ideal.LiesOver.tower_bot (g⁻¹ • Q₀) _ _⟩, ?_⟩
      exact card_under_eq_of_stabilizer_le hℓ (g⁻¹ • Q₀) hx
    · rintro ⟨⟨h𝔮p, h𝔮l⟩, h𝔮deg⟩
      haveI := h𝔮p
      haveI := h𝔮l
      obtain ⟨⟨Q, hQp, hQl⟩⟩ := Ideal.nonempty_primesOver (S := 𝓞 L) 𝔮
      haveI := hQp
      haveI := hQl
      haveI : Q.LiesOver (ratPrimeIdeal ℓ) := Ideal.LiesOver.trans Q 𝔮 _
      obtain ⟨g, hg⟩ := Ideal.exists_smul_eq_of_isGaloisGroup
        (ratPrimeIdeal ℓ) Q₀ Q (L ≃ₐ[ℚ] L)
      refine ⟨((g⁻¹ : L ≃ₐ[ℚ] L) : (L ≃ₐ[ℚ] L) ⧸ H), ?_, ?_⟩
      · refine (forall_smul_eq_iff_stabilizer_le Q₀ g⁻¹).mpr ?_
        rw [inv_inv, hg]
        refine stabilizer_le_of_card_under_eq (E := E) hℓ Q
          (hg ▸ inertia_smul_eq_bot hinertia g) ?_
        rw [← Q.over_def 𝔮]
        exact h𝔮deg
      · rw [restrictPrime_mk, inv_inv, hg]
        exact (Q.over_def 𝔮).symm
  rw [← himage]
  exact hinj.ncard_image

end S_FrobeniusDensity_ncard_degreeOne_primesOver_under
end P2MW
export P2MW.S_FrobeniusDensity_ncard_degreeOne_primesOver_under (solution)
