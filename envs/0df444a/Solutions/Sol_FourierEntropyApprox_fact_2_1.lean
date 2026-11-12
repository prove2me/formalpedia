-- Prove2me | solution 1 for FourierEntropyApprox.fact_2_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T23:04:06.428095+00:00
-- url     : https://prove2.me/submissions/5bf35b08-fdf9-409e-8563-6e4982430e0e

import Mathlib
import Definitions.Def_FourierEntropyApprox_fourierCoeff

section
set_option autoImplicit false
namespace FourierEntropyApprox.Dev.Plancherel
open FourierEntropyApprox

lemma spin_mul_self (b : Bool) : spin b * spin b = 1 := by
  cases b <;> simp [spin]

lemma sum_walsh_dual {n : ℕ} (x y : Cube n) :
    ∑ S : Finset (Fin n), walsh S x * walsh S y = if x = y then (2 : ℝ) ^ n else 0 := by
  have h : ∀ S : Finset (Fin n), walsh S x * walsh S y = ∏ i ∈ S, (spin (x i) * spin (y i)) := by
    intro S; unfold walsh; rw [Finset.prod_mul_distrib]
  simp_rw [h]
  have h2 := Finset.prod_one_add (s := (Finset.univ : Finset (Fin n))) (f := fun i => spin (x i) * spin (y i))
  rw [Finset.powerset_univ] at h2
  rw [← h2]
  split_ifs with hxy
  · subst hxy
    have : ∀ i : Fin n, 1 + spin (x i) * spin (x i) = 2 := by intro i; rw [spin_mul_self]; norm_num
    simp [this]
  · obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra hc; push Not at hc; exact hxy (funext hc)
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    revert hi
    cases hx : x i <;> cases hy : y i <;> simp [spin]

section general
variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

lemma avg_def (F : Cube n → 𝕜) : avg F = ((2 : 𝕜) ^ n)⁻¹ * ∑ x, F x := rfl

lemma fourierCoeff_def (f : Cube n → 𝕜) (S : Finset (Fin n)) :
    fourierCoeff f S = ((2 : 𝕜) ^ n)⁻¹ * ∑ x, f x * (walsh S x : 𝕜) := rfl

lemma cast_two_pow : (((2 : ℝ) ^ n : ℝ) : 𝕜) = (2 : 𝕜) ^ n := by rw [RCLike.ofReal_pow, RCLike.ofReal_ofNat]

lemma two_pow_ne_zero : ((2 : 𝕜) ^ n) ≠ 0 := pow_ne_zero _ two_ne_zero

/-- Fourier inversion `f x = ∑_S f̂(S) χ_S(x)`. -/
lemma fourier_inversion (f : Cube n → 𝕜) (x : Cube n) :
    ∑ S : Finset (Fin n), fourierCoeff f S * (walsh S x : 𝕜) = f x := by
  have hd : ∀ y : Cube n, ∑ S : Finset (Fin n), (walsh S y : 𝕜) * (walsh S x : 𝕜) =
      if y = x then (2 : 𝕜) ^ n else 0 := by
    intro y
    have := congrArg (fun r : ℝ => (r : 𝕜)) (sum_walsh_dual (n := n) y x)
    simp only [RCLike.ofReal_sum, RCLike.ofReal_mul] at this
    rw [this]; split_ifs <;> first | exact cast_two_pow | simp
  calc ∑ S : Finset (Fin n), fourierCoeff f S * (walsh S x : 𝕜)
      = ((2 : 𝕜) ^ n)⁻¹ * ∑ y, f y * ∑ S : Finset (Fin n), (walsh S y : 𝕜) * (walsh S x : 𝕜) := by
        simp_rw [fourierCoeff_def, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun S _ => by ring
    _ = f x := by
        simp_rw [hd]
        simp [mul_ite, Finset.sum_ite_eq']
        rw [mul_comm (f x), ← mul_assoc, inv_mul_cancel₀ two_pow_ne_zero, one_mul]

lemma star_fourierCoeff (f : Cube n → 𝕜) (S : Finset (Fin n)) :
    star (fourierCoeff f S) = ((2 : 𝕜) ^ n)⁻¹ * ∑ x, star (f x) * (walsh S x : 𝕜) := by
  rw [fourierCoeff_def]
  simp only [RCLike.star_def, map_mul, map_sum, map_inv₀, map_pow, map_ofNat, RCLike.conj_ofReal]

/-- Plancherel on the cube. -/
theorem plancherel (f g : Cube n → 𝕜) :
    cubeInner f g = ∑ S : Finset (Fin n), star (fourierCoeff f S) * fourierCoeff g S := by
  have h1 : ∀ x : Cube n, star (f x) * g x =
      ∑ S : Finset (Fin n), star (f x) * (fourierCoeff g S * (walsh S x : 𝕜)) := by
    intro x
    rw [← Finset.mul_sum, fourier_inversion]
  unfold cubeInner
  rw [avg_def]
  simp_rw [h1]
  simp_rw [star_fourierCoeff]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun x _ => ?_
  ring

end general
end FourierEntropyApprox.Dev.Plancherel

namespace FourierEntropyApprox
open FourierEntropyApprox.Dev.Plancherel in
theorem chk_fact_2_1 {n : ℕ} (f g : Cube n → ℂ) :
    cubeInner f g = ∑ S : Finset (Fin n), star (fourierCoeff f S) * fourierCoeff g S := by
  exact plancherel f g
end FourierEntropyApprox
end

theorem solution : type_of% @FourierEntropyApprox.chk_fact_2_1 := @FourierEntropyApprox.chk_fact_2_1
