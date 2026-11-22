-- Prove2me | solution 1 for BellSampling.Learn.bellProb_sum_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T21:41:07.920205+00:00
-- url     : https://prove2.me/submissions/4d083ffd-2ac0-4f70-a786-d9d17f380115

import Mathlib
import Definitions.Def_StabilizerRank
import Definitions.Def_BellSampling_Learn_Setting
import Theorems.Thm_BellSampling_Learn_lemma_2
open StabilizerRank
open BellSampling.Learn
set_option autoImplicit false

private lemma sum_sigma1_orth (a b a' b' : Bool) :
    (∑ c : ZMod 2 × ZMod 2, star (sigma1 c a b) * sigma1 c a' b') =
      if a = a' ∧ b = b' then (2 : ℂ) else 0 := by
  have huniv : (Finset.univ : Finset (ZMod 2 × ZMod 2)) =
      {(0, 0), (0, 1), (1, 0), (1, 1)} := by decide
  rw [huniv]
  cases a <;> cases b <;> cases a' <;> cases b' <;>
    simp [sigma1, sigma00, sigma01, sigma10, sigma11_eq, bitIdx] <;>
    norm_num

private lemma sum_sigma_orth {n : ℕ} (x y x' y' : Bits n) :
    (∑ r : PStr n, star (sigma r x y) * sigma r x' y') =
      if x = x' ∧ y = y' then (2 : ℂ) ^ n else 0 := by
  have hterm : ∀ r : PStr n,
      star (sigma r x y) * sigma r x' y' =
        ∏ i : Fin n, (star (sigma1 (r i) (x i) (y i)) * sigma1 (r i) (x' i) (y' i)) := by
    intro r
    simp only [sigma, Matrix.of_apply, star_prod, ← Finset.prod_mul_distrib]
  simp_rw [hterm]
  rw [← Fintype.prod_sum (fun (i : Fin n) (c : ZMod 2 × ZMod 2) =>
    star (sigma1 c (x i) (y i)) * sigma1 c (x' i) (y' i))]
  simp_rw [sum_sigma1_orth]
  by_cases hxy : x = x' ∧ y = y'
  · rcases hxy with ⟨rfl, rfl⟩
    simp
  · rw [if_neg hxy]
    have hex : ∃ i : Fin n, ¬(x i = x' i ∧ y i = y' i) := by
      by_contra hall
      exact hxy ⟨funext fun i => Classical.byContradiction fun hx => hall ⟨i, fun h => hx h.1⟩,
        funext fun i => Classical.byContradiction fun hy => hall ⟨i, fun h => hy h.2⟩⟩
    rcases hex with ⟨i, hi⟩
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem solution {n : ℕ} (ψ : QState n) (hψ : ∑ x, ‖ψ x‖ ^ 2 = 1) :
    ∑ r, bellProb ψ r = 1 := by
  simp_rw [BellSampling.Learn.lemma_2 ψ, ← Finset.sum_div]
  have h2n_ne : (2 : ℝ) ^ n ≠ 0 := by positivity
  rw [div_eq_one_iff_eq h2n_ne]
  suffices h_c : ((∑ r : PStr n, ‖∑ x, ∑ y, star (ψ x) * sigma r x y * star (ψ y)‖ ^ 2 : ℝ) : ℂ) =
      (((2 : ℝ) ^ n : ℝ) : ℂ) by
    exact Complex.ofReal_injective h_c
  push_cast
  have hnorm_c : ∀ z : ℂ, (‖z‖ : ℂ) ^ 2 = star z * z := by
    intro z
    have h1 : ((‖z‖ ^ 2 : ℝ) : ℂ) = star z * z := by
      rw [← Complex.normSq_eq_norm_sq, Complex.star_def, Complex.normSq_eq_conj_mul_self]
    simpa using h1
  simp_rw [hnorm_c]
  have h_expand : ∀ r : PStr n,
      star (∑ x, ∑ y, star (ψ x) * sigma r x y * star (ψ y)) *
        (∑ x', ∑ y', star (ψ x') * sigma r x' y' * star (ψ y')) =
      ∑ x, ∑ y, ∑ x', ∑ y',
        (ψ x * ψ y * star (ψ x') * star (ψ y')) *
          (star (sigma r x y) * sigma r x' y') := by
    intro r
    rw [star_sum]
    simp_rw [star_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    simp_rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun y' _ => ?_
    simp only [star_mul', star_star]
    ring
  simp_rw [h_expand]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := Finset.univ (α := PStr n))]
  simp_rw [← Finset.mul_sum, sum_sigma_orth]
  have h_diag : ∀ x y : Bits n,
      (∑ x', ∑ y',
        ψ x * ψ y * star (ψ x') * star (ψ y') *
          if x = x' ∧ y = y' then (2 : ℂ) ^ n else 0) =
        (2 : ℂ) ^ n * (star (ψ x) * ψ x) * (star (ψ y) * ψ y) := by
    intro x y
    have h1 : ∀ x' : Bits n,
        (∑ y', ψ x * ψ y * star (ψ x') * star (ψ y') *
          if x = x' ∧ y = y' then (2 : ℂ) ^ n else 0) =
        if x = x' then ψ x * ψ y * star (ψ x') * star (ψ y) * (2 : ℂ) ^ n else 0 := by
      intro x'
      by_cases hx : x = x'
      · subst hx
        simp
      · simp [hx]
    simp_rw [h1]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    ring
  simp_rw [h_diag, ← hnorm_c]
  have h_factor :
      (∑ x : Bits n, ∑ y : Bits n, (2 : ℂ) ^ n * (‖ψ x‖ : ℂ) ^ 2 * (‖ψ y‖ : ℂ) ^ 2) =
        (2 : ℂ) ^ n * (∑ x : Bits n, (‖ψ x‖ : ℂ) ^ 2) * (∑ y : Bits n, (‖ψ y‖ : ℂ) ^ 2) := by
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
  rw [h_factor]
  have h_cast : (∑ x : Bits n, (‖ψ x‖ : ℂ) ^ 2) = ((∑ x : Bits n, ‖ψ x‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [h_cast, hψ]
  simp
