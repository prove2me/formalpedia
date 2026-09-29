-- Prove2me | solution 1 for CuspidalType.exists_sq_ne_one_and_forall_apply_eq_zero_iff_of_card_eq_of_forall_apply_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/87c4c4be-500d-5ff9-ba44-9c1b453d9879

import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Theorems.Thm_CuspidalType_pow_add_one_eq_one_iff_forall_theta_scalarUnit_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspidalType_exists_sq_ne_one_and_forall_apply_eq_zero_iff_of_card_eq_of_forall_apply_pow_eq

set_option autoImplicit false

open Polynomial CuspidalType

open Finset

theorem solution
    {q : ℕ} [Fact q.Prime] {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (m : ((GaloisField q 2)ˣ →* Kˣ) →₀ ℕ)
    (S₀ : Finset ((GaloisField q 2)ˣ →* Kˣ)) (hS₀ : ∀ μ : (GaloisField q 2)ˣ →* Kˣ,
      μ ∈ S₀ ↔ ∀ c : (ZMod q)ˣ, μ (Units.map (algebraMap (ZMod q) (GaloisField q 2)).toMonoidHom c) = 1) (hcard : S₀.card = q + 1)
    (hle : ∀ μ, m μ ≤ 1) (h1 : m 1 = 1) (hsupp : ∀ μ ∈ m.support, μ ∈ S₀)
    (hsum : (m.sum fun _ n => n) = q - 1) (hsym : ∀ μ, m (μ ^ q) = m μ) :
    ∃ θ ∈ S₀, θ ^ 2 ≠ 1 ∧ ∀ μ ∈ S₀, m μ = 0 ↔ (μ = θ ∨ μ = θ⁻¹) := by
  classical

  have hpow : ∀ μ ∈ S₀, μ ^ q = μ⁻¹ := fun μ hμ => by
    have h : μ ^ (q + 1) = 1 :=
      (CuspidalType.pow_add_one_eq_one_iff_forall_theta_scalarUnit_eq_one μ).2 ((hS₀ μ).1 hμ)
    refine MonoidHom.ext fun x => ?_
    have hx := DFunLike.congr_fun h x
    rw [MonoidHom.pow_apply, MonoidHom.one_apply, pow_succ] at hx
    rw [MonoidHom.pow_apply, MonoidHom.inv_apply]
    exact eq_inv_of_mul_eq_one_left hx
  have hinvS : ∀ μ ∈ S₀, μ⁻¹ ∈ S₀ := fun μ hμ => (hS₀ _).2 fun c => by
    rw [MonoidHom.inv_apply, (hS₀ μ).1 hμ c, inv_one]

  obtain ⟨M, hM⟩ : ∃ M : Finset ((GaloisField q 2)ˣ →* Kˣ), M = S₀.filter (fun μ => m μ = 0) := ⟨_, rfl⟩
  have hmemM : ∀ μ, μ ∈ M ↔ μ ∈ S₀ ∧ m μ = 0 := fun μ => by rw [hM, mem_filter]
  have hMinv : ∀ μ ∈ M, μ⁻¹ ∈ M := by
    intro μ hμ
    rw [hmemM] at hμ ⊢
    exact ⟨hinvS μ hμ.1, by rw [← hpow μ hμ.1, hsym]; exact hμ.2⟩
  have h1M : (1 : (GaloisField q 2)ˣ →* Kˣ) ∉ M := fun h => by
    have := ((hmemM 1).1 h).2
    omega

  have hsuppEq : m.support = S₀.filter (fun μ => ¬ m μ = 0) := by
    ext μ
    simp only [Finsupp.mem_support_iff, mem_filter]
    exact ⟨fun h => ⟨hsupp μ (Finsupp.mem_support_iff.2 h), h⟩, fun h => h.2⟩
  have hcardP : (S₀.filter (fun μ => ¬ m μ = 0)).card = q - 1 := by
    rw [← hsuppEq, ← hsum, Finsupp.sum, card_eq_sum_ones]
    refine sum_congr rfl fun μ hμ => ?_
    have hμ1 := hle μ
    have hμ0 := Finsupp.mem_support_iff.1 hμ
    omega
  have hcardM : M.card = 2 := by
    have hsplit := card_filter_add_card_filter_not (s := S₀) (fun μ => m μ = 0)
    have hq := (Fact.out : q.Prime).two_le
    rw [← hM, hcardP, hcard] at hsplit
    omega
  obtain ⟨θ₁, θ₂, hne, hM12⟩ := card_eq_two.1 hcardM
  have hθ₁M : θ₁ ∈ M := by rw [hM12]; simp
  have hθ₂M : θ₂ ∈ M := by rw [hM12]; simp

  obtain ⟨β, hβ⟩ := IsCyclic.exists_generator (α := (GaloisField q 2)ˣ)
  have hgen : ∀ μ ν : (GaloisField q 2)ˣ →* Kˣ, μ β = ν β → μ = ν := by
    intro μ ν h
    refine MonoidHom.ext fun x => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hβ x)
    rw [map_zpow, map_zpow, h]
  have hself : ∀ μ : (GaloisField q 2)ˣ →* Kˣ, μ⁻¹ = μ → μ ≠ 1 → μ β = -1 := by
    intro μ hinv hne1
    have hβinv : (μ β)⁻¹ = μ β := by rw [← MonoidHom.inv_apply, hinv]
    rcases (Units.inv_eq_self_iff _).1 hβinv with h | h
    · exact absurd (hgen μ 1 (by rw [h, MonoidHom.one_apply])) hne1
    · exact h
  by_cases h12 : θ₁⁻¹ = θ₂
  · refine ⟨θ₁, ((hmemM θ₁).1 hθ₁M).1, fun hsq => hne ?_, fun μ hμ => ?_⟩
    · rw [← h12]
      refine MonoidHom.ext fun x => ?_
      have hx := DFunLike.congr_fun hsq x
      rw [MonoidHom.pow_apply, MonoidHom.one_apply, sq] at hx
      rw [MonoidHom.inv_apply]
      exact (inv_eq_of_mul_eq_one_right hx).symm
    · rw [h12]
      have hiff : μ ∈ M ↔ μ = θ₁ ∨ μ = θ₂ := by rw [hM12]; simp
      rw [← hiff, hmemM]
      exact ⟨fun h => ⟨hμ, h⟩, fun h => h.2⟩
  · exfalso
    have h11 : θ₁⁻¹ = θ₁ := by
      have h := hMinv θ₁ hθ₁M
      rw [hM12, mem_insert, mem_singleton] at h
      exact h.resolve_right h12
    have h22 : θ₂⁻¹ = θ₂ := by
      have h := hMinv θ₂ hθ₂M
      rw [hM12, mem_insert, mem_singleton] at h
      rcases h with h | h
      · exact absurd (MonoidHom.ext fun x => by rw [← h, MonoidHom.inv_apply, MonoidHom.inv_apply, inv_inv]) h12
      · exact h
    have hne1 : θ₁ ≠ 1 := fun h => h1M (h ▸ hθ₁M)
    have hne2 : θ₂ ≠ 1 := fun h => h1M (h ▸ hθ₂M)
    exact hne (hgen θ₁ θ₂ (by rw [hself θ₁ h11 hne1, hself θ₂ h22 hne2]))

end S_CuspidalType_exists_sq_ne_one_and_forall_apply_eq_zero_iff_of_card_eq_of_forall_apply_pow_eq
end P2MW
export P2MW.S_CuspidalType_exists_sq_ne_one_and_forall_apply_eq_zero_iff_of_card_eq_of_forall_apply_pow_eq (solution)
