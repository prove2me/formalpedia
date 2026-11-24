-- Prove2me | solution 1 for Formalism.NG.idemLift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:54:16.306835+00:00
-- url     : https://prove2.me/submissions/d9ed21ab-d8fe-4c2c-828b-190618fb3320

import Definitions.Def_Formalism_CharacterColumnKernels_StatOntoLattice
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SpacedProductLowerBound
import Theorems.Thm_Formalism_NG_IdemLiftAlt_X_dvd_nP
import Theorems.Thm_Formalism_NG_IdemLiftAlt_newton
import Theorems.Thm_Formalism_NG_IdemLiftAlt_limit_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.NG
open IdemLiftAlt
namespace Formalism.NG
theorem _root_.solution : IdempotentLift := by
  intro O A B _ _ _ _ _ _ _ _ f hf hnil e₁ e₂ h1 h2 h12 h21
  set I := IsLocalRing.maximalIdeal O
  let K : Submodule O A := (RingHom.ker f).restrictScalars O
  have hK : ∀ x, x ∈ K ↔ f x = 0 := fun x => by simp [K, RingHom.mem_ker]
  have hfa : ∀ (x : A) (k : ℕ), f (aeval x (nP k)) = aeval (f x) (nP k) := by
    intro x k
    exact (Polynomial.aeval_algHom_apply f.toIntAlgHom x (nP k)).symm
  have hidem : ∀ (e : B), IsIdempotentElem e → ∀ k, aeval e (nP k) = e := by
    intro e he k
    induction k with
    | zero => simp [nP]
    | succ k ih =>
      have he2 : e ^ 2 = e := by rw [pow_two]; exact he
      have he3 : e ^ 3 = e := by rw [pow_succ, he2]; exact he
      simp only [nP, map_sub, map_mul, map_pow, ih, map_ofNat]
      rw [he2, he3]
      noncomm_ring
  have lift : ∀ (a : A), IsIdempotentElem (f a) → ∃ n L, IsIdempotentElem L ∧
      (∀ j : ℕ, aeval a (nP (n + j)) - L ∈ I ^ j • (⊤ : Submodule O A)) ∧ f L = f a := by
    intro a ha
    have hx : f (a ^ 2 - a) = 0 := by
      rw [map_sub, map_pow, pow_two, ha, sub_self]
    obtain ⟨n, hn⟩ := hnil _ hx
    obtain ⟨L, hLi, hL⟩ := newton a n hn
    refine ⟨n, L, hLi, hL, ?_⟩
    have hq := limit_map a L n hL K.mkQ (K.mkQ a) (fun k => by
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hK, map_sub, hfa,
        hidem _ ha, sub_self])
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hK, map_sub,
      sub_eq_zero] at hq
    exact hq
  obtain ⟨a₁, rfl⟩ := hf e₁
  obtain ⟨n₁, E₁, hE₁, -, hfE₁⟩ := lift a₁ h1
  obtain ⟨b, rfl⟩ := hf e₂
  set a₂ : A := (1 - E₁) * b * (1 - E₁) with ha₂
  have hfa₂ : f a₂ = f b := by
    rw [ha₂, map_mul, map_mul, map_sub, map_one, hfE₁]
    have e : (1 - f a₁) * f b * (1 - f a₁) =
        f b - f a₁ * f b - f b * f a₁ + f a₁ * (f b * f a₁) := by noncomm_ring
    rw [e, h12, h21]; simp
  obtain ⟨n₂, E₂, hE₂, hL₂, hfE₂⟩ := lift a₂ (by rw [hfa₂]; exact h2)
  have hE1c : E₁ * (1 - E₁) = 0 := by rw [mul_sub, mul_one, hE₁.eq, sub_self]
  have hE1c' : (1 - E₁) * E₁ = 0 := by rw [sub_mul, one_mul, hE₁.eq, sub_self]
  have hl : E₁ * a₂ = 0 := by rw [ha₂, ← mul_assoc, ← mul_assoc, hE1c]; simp
  have hr : a₂ * E₁ = 0 := by rw [ha₂, mul_assoc, hE1c']; simp
  have hseq : ∀ k, E₁ * aeval a₂ (nP k) = 0 ∧ aeval a₂ (nP k) * E₁ = 0 := by
    intro k
    obtain ⟨R, hR⟩ := X_dvd_nP k
    have h' : aeval a₂ (nP k) = a₂ * aeval a₂ R := by rw [hR, map_mul, aeval_X]
    have h'' : aeval a₂ (nP k) = aeval a₂ R * a₂ := by rw [hR, mul_comm, map_mul, aeval_X]
    constructor
    · rw [h', ← mul_assoc, hl, zero_mul]
    · rw [h'', mul_assoc, hr, mul_zero]
  have h12' : E₁ * E₂ = 0 :=
    limit_map a₂ E₂ n₂ hL₂ (LinearMap.mulLeft O E₁) 0 (fun k => (hseq k).1)
  have h21' : E₂ * E₁ = 0 :=
    limit_map a₂ E₂ n₂ hL₂ (LinearMap.mulRight O E₁) 0 (fun k => (hseq k).2)
  exact ⟨E₁, E₂, hE₁, hE₂, h12', h21', hfE₁, by rw [hfE₂, hfa₂]⟩
end Formalism.NG
