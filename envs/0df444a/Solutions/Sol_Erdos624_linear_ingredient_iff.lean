-- Prove2me | solution 1 for Erdos624.linear_ingredient_iff
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-24T15:29:23.240921+00:00
-- url     : https://prove2.me/submissions/09dbbfe0-8442-4568-85d6-8f46b1648122

import Mathlib
open Finset

namespace E624R12
open Module

lemma exists_ne_zero_one_of_card {F : Type*} [Field F] [Finite F] (h : 2 < Nat.card F) :
    ∃ α : F, α ≠ 0 ∧ α ≠ 1 := by
  classical
  have := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card] at h
  by_contra hcon
  push Not at hcon
  have hsub : (Finset.univ : Finset F) ⊆ {0, 1} := by
    intro x _
    by_cases hx : x = 0
    · simp [hx]
    · simp [hcon x hx]
  have := Finset.card_le_card hsub
  rw [Finset.card_univ] at this
  have h2 : ({0, 1} : Finset F).card ≤ 2 := Finset.card_le_two
  omega

theorem linear_ingredient (d : ℕ) (hd : 2 ≤ d) :
    ∃ T : (Fin d → ZMod 2) →ₗ[ZMod 2] (Fin d → ZMod 2),
      Function.Bijective T ∧ Function.Bijective (fun v => v + T v) := by
  have hd0 : d ≠ 0 := by omega
  let F := GaloisField 2 d
  have hcard : Nat.card F = 2 ^ d := GaloisField.card 2 d hd0
  have hrank : finrank (ZMod 2) F = d := GaloisField.finrank 2 hd0
  have h4 : 2 < Nat.card F := by
    rw [hcard]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
  obtain ⟨α, hα0, hα1⟩ := exists_ne_zero_one_of_card h4
  let e : F ≃ₗ[ZMod 2] (Fin d → ZMod 2) :=
    LinearEquiv.ofFinrankEq F (Fin d → ZMod 2) (by rw [hrank, Module.finrank_fin_fun])
  let M : F →ₗ[ZMod 2] F := LinearMap.mulLeft (ZMod 2) α
  refine ⟨e.toLinearMap ∘ₗ M ∘ₗ e.symm.toLinearMap, ?_, ?_⟩
  · have hM : Function.Bijective M := by
      constructor
      · intro x y h; simpa [M, hα0] using h
      · intro y; exact ⟨α⁻¹ * y, by simp only [M, LinearMap.mulLeft_apply]; rw [← mul_assoc, mul_inv_cancel₀ hα0, one_mul]⟩
    exact e.bijective.comp (hM.comp e.symm.bijective)
  · have hβ : (1 + α : F) ≠ 0 := by
      intro h
      apply hα1
      have hα : α = -1 := eq_neg_of_add_eq_zero_right h
      rw [hα, CharTwo.neg_eq]
    let M' : F →ₗ[ZMod 2] F := LinearMap.mulLeft (ZMod 2) (1 + α)
    have hM' : Function.Bijective M' := by
      constructor
      · intro x y h; simpa [M', hβ] using h
      · intro y; exact ⟨(1 + α)⁻¹ * y, by simp only [M', LinearMap.mulLeft_apply]; rw [← mul_assoc, mul_inv_cancel₀ hβ, one_mul]⟩
    have heq : (fun v => v + (e.toLinearMap ∘ₗ M ∘ₗ e.symm.toLinearMap) v) =
        e.toLinearMap ∘ₗ M' ∘ₗ e.symm.toLinearMap := by
      funext v
      simp only [LinearMap.comp_apply, M, M', LinearMap.mulLeft_apply, LinearEquiv.coe_coe]
      rw [add_mul, one_mul, map_add, LinearEquiv.apply_symm_apply]
    rw [heq]
    exact e.bijective.comp (hM'.comp e.symm.bijective)

theorem linear_ingredient_one :
    ¬ ∃ T : (Fin 1 → ZMod 2) →ₗ[ZMod 2] (Fin 1 → ZMod 2),
      Function.Bijective T ∧ Function.Bijective (fun v => v + T v) := by
  rintro ⟨T, hT, hIT⟩
  have hall : ∀ v : Fin 1 → ZMod 2, v = 0 ∨ v = fun _ => 1 := by
    intro v
    have : v 0 = 0 ∨ v 0 = 1 := by
      generalize v 0 = z; fin_cases z
      · left; rfl
      · right; rfl
    rcases this with h | h
    · left; funext i; fin_cases i; simpa using h
    · right; funext i; fin_cases i; simpa using h
  have hne : (fun _ => (1 : ZMod 2)) ≠ (0 : Fin 1 → ZMod 2) := by
    intro h; have := congrFun h 0; simp at this
  rcases hall (T (fun _ => 1)) with h | h
  · apply hne; apply hT.1; rw [h, map_zero]
  · apply hne; apply hIT.1
    show (fun _ => (1 : ZMod 2)) + T (fun _ => 1) = (0 : Fin 1 → ZMod 2) + T 0
    rw [map_zero, h]
    funext i; simp; decide

theorem linear_ingredient_iff (d : ℕ) :
    (∃ T : (Fin d → ZMod 2) →ₗ[ZMod 2] (Fin d → ZMod 2),
      Function.Bijective T ∧ Function.Bijective (fun v => v + T v)) ↔ d ≠ 1 := by
  constructor
  · rintro h rfl; exact linear_ingredient_one h
  · intro hd
    rcases Nat.lt_or_ge d 2 with h | h
    · have : d = 0 := by omega
      subst this
      refine ⟨0, ?_, ?_⟩ <;>
      · constructor
        · intro x y _; funext i; exact i.elim0
        · intro y; exact ⟨y, by funext i; exact i.elim0⟩
    · exact linear_ingredient d h
end E624R12

namespace Erdos624

theorem linear_ingredient_iff (d : ℕ) :
    (∃ T : (Fin d → ZMod 2) →ₗ[ZMod 2] (Fin d → ZMod 2),
      Function.Bijective T ∧ Function.Bijective (fun v => v + T v)) ↔ d ≠ 1 := by
  exact E624R12.linear_ingredient_iff d

end Erdos624

open Finset

theorem solution (d : ℕ) :
    (∃ T : (Fin d → ZMod 2) →ₗ[ZMod 2] (Fin d → ZMod 2),
      Function.Bijective T ∧ Function.Bijective (fun v => v + T v)) ↔ d ≠ 1 :=
  Erdos624.linear_ingredient_iff d
