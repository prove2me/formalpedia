-- Prove2me | solution 1 for CuspidalType.exists_sq_ne_one_and_forall_charpoly_torus_mul_eq_prod_of_forall_character_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/0c4ec67a-6cfe-5cf8-8580-ac89aa8f9515

import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Theorems.Thm_Representation_exists_multiplicity_of_isCyclic
import Theorems.Thm_CuspidalType_torus_unitsMap_algebraMap
import Theorems.Thm_CuspidalType_sum_character_torus_and_sum_character_torus_mul_character_torus_inv
import Theorems.Thm_Finsupp_forall_apply_le_one_and_apply_one_eq_one_of_sum_eq_card_of_sum_mul_eq
import Theorems.Thm_CuspidalType_finsupp_apply_pow_eq_of_forall_character_torus_eq_sum
import Theorems.Thm_CuspidalType_exists_finset_monoidHom_mem_iff_forall_apply_eq_one_and_card_eq
import Theorems.Thm_CuspidalType_exists_sq_ne_one_and_forall_apply_eq_zero_iff_of_card_eq_of_forall_apply_pow_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspidalType_exists_sq_ne_one_and_forall_charpoly_torus_mul_eq_prod_of_forall_character_eq

set_option autoImplicit false

open Polynomial CuspidalType

theorem solution
    {q : ℕ} [Fact q.Prime] {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nontrivial V]
    (ρ : Representation K (GL2 q) V)
    (hcent : ∀ c : (ZMod q)ˣ, ρ (scalarElem q c) = LinearMap.id)
    (hK1 : Module.finrank K V = q - 1)
    (hK2 : ∀ (c : (ZMod q)ˣ) (g : GL2 q), ρ.character (scalarElem q c * g) = ρ.character g)
    (hK3 : ∀ t : ZMod q, t ≠ 0 → ρ.character (unipotent q t) = -1)
    (hK4 : ∀ (a : (ZMod q)ˣ) (s : ZMod q), a ≠ 1 → ρ.character (unipotent q s * diagElem q a) = 0)
    (hK5 : ∑ g : GL2 q, ρ.character g = 0)
    (hK6 : ∑ g : GL2 q, ρ.character g * ρ.character g⁻¹ = Nat.card (GL2 q))
    (S₀ : Finset ((GaloisField q 2)ˣ →* Kˣ)) (hS₀ : ∀ μ : (GaloisField q 2)ˣ →* Kˣ,
      μ ∈ S₀ ↔ ∀ c : (ZMod q)ˣ, μ (Units.map (algebraMap (ZMod q) (GaloisField q 2)).toMonoidHom c) = 1) :
    ∃ θ ∈ S₀, θ ^ 2 ≠ 1 ∧ ∀ α : (GaloisField q 2)ˣ,
      (ρ (torus q α)).charpoly * ((X - C ((θ α : Kˣ) : K)) * (X - C (((θ α)⁻¹ : Kˣ) : K))) =
        ∏ μ ∈ S₀, (X - C ((μ α : Kˣ) : K)) := by
  classical
  haveI : Fintype (GaloisField q 2)ˣ := Fintype.ofFinite _

  obtain ⟨m, htr, hcp, hsum, hfix⟩ := Representation.exists_multiplicity_of_isCyclic (ρ.comp (torus q))
  have htr' : ∀ α : (GaloisField q 2)ˣ,
      ρ.character (torus q α) = m.sum fun μ n => (n : K) * ((μ α : Kˣ) : K) := fun α => htr α

  obtain ⟨hS1, hS2⟩ :=
    CuspidalType.sum_character_torus_and_sum_character_torus_mul_character_torus_inv ρ hK1 hK2 hK3 hK4 hK5 hK6

  have hcardT : Fintype.card (GaloisField q 2)ˣ = q ^ 2 - 1 := by
    rw [Fintype.card_eq_nat_card, Nat.card_units, GaloisField.card q 2 two_ne_zero]
  have hsumN : (m.sum fun _ n => n) = q - 1 := hsum.trans hK1
  have hsumK : (m.sum fun _ n => (n : K)) = ((q - 1 : ℕ) : K) := by
    rw [← hsumN]; simp only [Finsupp.sum, Nat.cast_sum]

  obtain ⟨hle, hm1⟩ := Finsupp.forall_apply_le_one_and_apply_one_eq_one_of_sum_eq_card_of_sum_mul_eq m
    (fun α => ρ.character (torus q α)) htr'
    (by rw [hS1, hcardT])
    (by
      have : ∀ α : (GaloisField q 2)ˣ, ρ.character (torus q α⁻¹) = ρ.character (torus q α)⁻¹ := fun α => by
        rw [map_inv]
      simp only [this]
      rw [hS2, hsumK, hcardT, Nat.cast_mul])

  have hsupp : ∀ μ ∈ m.support, μ ∈ S₀ := fun μ hμ => (hS₀ μ).2 fun c => hfix μ hμ _ (by
    show ρ (torus q (Units.map (algebraMap (ZMod q) (GaloisField q 2)).toMonoidHom c)) = LinearMap.id
    rw [CuspidalType.torus_unitsMap_algebraMap, hcent])

  have hsym : ∀ μ, m (μ ^ q) = m μ :=
    CuspidalType.finsupp_apply_pow_eq_of_forall_character_torus_eq_sum ρ m htr'
  obtain ⟨S₁, hS₁, hcard₁⟩ :=
    CuspidalType.exists_finset_monoidHom_mem_iff_forall_apply_eq_one_and_card_eq q K
  have hSS : S₀ = S₁ := Finset.ext fun μ => (hS₀ μ).trans (hS₁ μ).symm
  have hcard : S₀.card = q + 1 := hSS ▸ hcard₁

  obtain ⟨θ, hθS, hθ2, hmiss⟩ :=
    CuspidalType.exists_sq_ne_one_and_forall_apply_eq_zero_iff_of_card_eq_of_forall_apply_pow_eq
      m S₀ hS₀ hcard hle hm1 hsupp hsumN hsym
  refine ⟨θ, hθS, hθ2, fun α => ?_⟩
  have hθinvS : θ⁻¹ ∈ S₀ := (hS₀ _).2 fun c => by
    rw [MonoidHom.inv_apply, (hS₀ θ).1 hθS c, inv_one]
  have hne : θ ≠ θ⁻¹ := fun h => hθ2 (by rw [sq]; exact inv_eq_iff_mul_eq_one.mp h.symm)
  have hsuppEq : m.support = S₀ \ {θ, θ⁻¹} := by
    ext μ
    simp only [Finsupp.mem_support_iff, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hμ
      have hμS : μ ∈ S₀ := hsupp μ (Finsupp.mem_support_iff.2 hμ)
      exact ⟨hμS, fun h => hμ ((hmiss μ hμS).2 h)⟩
    · rintro ⟨hμS, h⟩ h0
      exact h ((hmiss μ hμS).1 h0)
  have hcpα : (ρ (torus q α)).charpoly = ∏ μ ∈ S₀ \ {θ, θ⁻¹}, (X - C ((μ α : Kˣ) : K)) := by
    have h := hcp α
    rw [show (ρ.comp (torus q)) α = ρ (torus q α) from rfl] at h
    rw [h, Finsupp.prod, hsuppEq]
    refine Finset.prod_congr rfl fun μ hμ => ?_
    have hμ1 : m μ = 1 := by
      have h1 := hle μ
      have h2 : m μ ≠ 0 := by rw [← Finsupp.mem_support_iff, hsuppEq]; exact hμ
      omega
    rw [hμ1, pow_one]
  have hpair : ({θ, θ⁻¹} : Finset ((GaloisField q 2)ˣ →* Kˣ)) ⊆ S₀ := by
    intro μ hμ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hμ
    rcases hμ with rfl | rfl
    exacts [hθS, hθinvS]
  rw [hcpα, ← Finset.prod_sdiff hpair, Finset.prod_pair hne, MonoidHom.inv_apply]

end S_CuspidalType_exists_sq_ne_one_and_forall_charpoly_torus_mul_eq_prod_of_forall_character_eq
end P2MW
export P2MW.S_CuspidalType_exists_sq_ne_one_and_forall_charpoly_torus_mul_eq_prod_of_forall_character_eq (solution)
