-- Prove2me | solution 1 for BooleanFun.BV.almost_character
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:15:11.912628+00:00
-- url     : https://prove2.me/submissions/dec935a5-ed02-4144-9d35-58325fe087de

import Definitions.Def_BooleanFun_Basic
import Definitions.Def_BooleanFun_BooleanValued
import Theorems.Thm_BooleanFun_BV_fourier_eq_one
import Theorems.Thm_BooleanFun_BV_walsh_boolean_valued
import Theorems.Thm_BooleanFun_BV_inner_eq_distance
import Theorems.Thm_BooleanFun_BV_acceptanceProbabilityBLR_eq
import Theorems.Thm_BooleanFun_fourier_convolution
import Theorems.Thm_BooleanFun_fourier_eq_inner
import Theorems.Thm_BooleanFun_inner_eq_expectation
import Theorems.Thm_BooleanFun_inner_eq_sum_fourier

section
noncomputable section
namespace BooleanFun
open BooleanFun Finset Function Fin RealInnerProductSpace
variable {n : ℕ} {f g : BooleanFunc n} {x : Fin n → Fin 2}
namespace BV
section DegreeOne
end DegreeOne
section Distance
end Distance
section BLR
private lemma _aux_lemma : (𝐄 <| fun x ↦ 𝐄 <| fun y ↦ (1/2) * (1 + (f x) * (f y) * (f (x + y))))
    = (1/2) * (1 + (𝐄 <| fun x ↦ (f x) * (𝐄 <| fun y ↦ (f y) * (f (x + y))))) := by
    unfold expectation
    dsimp
    conv => enter [1, 2, 2, x]; rw [← mul_sum, sum_add_distrib, mul_add, mul_add]
            simp; arg 2; rw [← mul_assoc, mul_comm _ 2⁻¹, mul_assoc]
            enter [2, 2, 2, y]; rw [mul_assoc]
    conv => enter [1, 2, 2, x, 2]; rw [← mul_sum]
            rw [← mul_assoc, ← mul_assoc, mul_comm _ (f x), ← mul_assoc, mul_comm (f x) _]
            rw [mul_assoc, mul_assoc]
    rw [sum_add_distrib, Finset.sum_const]
    simp
    rw [← mul_sum, ← mul_add, ← mul_assoc, mul_comm _ 2⁻¹, mul_assoc]
    rw [mul_add, inv_mul_cancel₀ (by simp)]
end BLR
end BV
end BooleanFun
end
end

set_option autoImplicit false
noncomputable section
open BooleanFun
open BooleanFun Finset Function Fin RealInnerProductSpace
variable {n : ℕ} {f g : BooleanFunc n} {x : Fin n → Fin 2}
open BooleanFun.BV
namespace BooleanFun.BV
theorem _root_.solution (hbv : BooleanValued f) {ε : ℝ} (h : acceptanceProbabilityBLR f ≥ 1 - ε):
    ∃ S, distance f (χ S) ≤ ε := by
  have : 1-ε ≤ (1/2) * (1 + ∑ S, (𝓕 f S) * (𝓕 f S)^2) := by
    calc
      _ ≤ acceptanceProbabilityBLR f := h
      _ = (𝐄 $ fun x ↦ 𝐄 $ fun y ↦ (1/2) * (1 + (f x) * (f y) * (f (x + y)))) :=
        acceptanceProbabilityBLR_eq hbv
      _ = (1/2) * (1 + (𝐄 $ fun x ↦ (f x) * (𝐄 $ fun y ↦ (f y) * (f (x + y))))) := _aux_lemma
      _ = (1/2) * (1 + (𝐄 $ fun x ↦ (f x) * (f⋆f) x)) := rfl
      _ = (1/2) * (1 + 𝐄 (f * (f⋆f))) := rfl
      _ = (1/2) * (1 + ∑ S, (𝓕 f S) * (𝓕 (f⋆f) S)) := by
        rw [← inner_eq_expectation, inner_eq_sum_fourier]
      _ = _ := by rw [fourier_convolution]; simp_rw [Pi.mul_apply, pow_two]
  have : ∃ S₀, ∀ S, 𝓕 f S ≤ 𝓕 f S₀ := Finite.exists_max (𝓕 f ·)
  obtain ⟨S₀, hS₀⟩ := this
  have : 1-2 * ε ≤ 1-2 * distance f (χ S₀) := by
    calc
      _ ≤ ∑ S, (𝓕 f S) * (𝓕 f S)^2  := by linarith
      _ ≤ ∑ S, (𝓕 f S₀) * (𝓕 f S)^2 := by gcongr; exact hS₀ _
      _ ≤ (𝓕 f S₀) * ∑ S, |𝓕 f S|^2 := by simp_rw [sq_abs]; rw [mul_sum]
      _ = 𝓕 f S₀                  := by rw [fourier_eq_one hbv, mul_one]
      _ = ⟪f, χ S₀⟫                := by rw [fourier_eq_inner, real_inner_comm]
      _ = _                        := inner_eq_distance hbv (walsh_boolean_valued S₀)
  use S₀
  linarith
end BooleanFun.BV
