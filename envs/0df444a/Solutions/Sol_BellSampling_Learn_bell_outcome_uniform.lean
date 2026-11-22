-- Prove2me | solution 1 for BellSampling.Learn.bell_outcome_uniform
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T21:38:07.842523+00:00
-- url     : https://prove2.me/submissions/a0bc7a4a-84fd-455d-929b-887eb496d8d3

import Mathlib
import Definitions.Def_StabilizerRank
import Definitions.Def_BellSampling_Learn_Setting
import Theorems.Thm_BellSampling_Learn_conj_eq_sigmaZ
import Theorems.Thm_BellSampling_Learn_eq_1
import Theorems.Thm_BellSampling_Learn_sigma_mul
import Theorems.Thm_BellSampling_Learn_expect_eq_zero_of_not_mem
open StabilizerRank
open BellSampling.Learn
set_option autoImplicit false

private lemma sigma1_zero : sigma1 (0, 0) = 1 := by
  ext a b
  cases a <;> cases b <;> simp [sigma1, sigma00, bitIdx]

private lemma sigma_zero (n : ℕ) : sigma (0 : PStr n) = 1 := by
  ext x y
  have h0 : ∀ i : Fin n, sigma1 ((0 : PStr n) i) (x i) (y i) = if x i = y i then 1 else 0 := by
    intro i
    have hs : (0 : PStr n) i = (0, 0) := rfl
    rw [hs, sigma1_zero]
    rfl
  simp_rw [sigma, Matrix.of_apply, h0]
  by_cases hxy : x = y
  · subst hxy
    simp
  · have h_ex : ∃ i : Fin n, x i ≠ y i := by
      by_contra h_all
      exact hxy (funext fun i => not_ne_iff.mp (fun hne => h_all ⟨i, hne⟩))
    rcases h_ex with ⟨i, hi⟩
    rw [Finset.prod_eq_zero (Finset.mem_univ i), Matrix.one_apply_ne hxy]
    exact if_neg hi

private lemma stabilizer_norm_eq_one {n : ℕ} (ψ : QState n) (hψ : IsStabilizerState ψ) :
    ∑ x : Bits n, star (ψ x) * ψ x = 1 := by
  rcases hψ with ⟨U, ⟨hU_unit, _⟩, rfl⟩
  have hU : U.conjTranspose * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU_unit
  have hdot : star (U.mulVec (zeroState n)) ⬝ᵥ (U.mulVec (zeroState n)) = 1 := by
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hU,
      Matrix.vecMul_one]
    simp [dotProduct, zeroState]
  simpa [dotProduct, Pi.star_apply] using hdot

theorem solution {n : ℕ} (ψ : QState n) (hψ : IsStabilizerState ψ) :
    ∃ s : PStr n, ∀ r : PStr n,
      (r + s ∈ stabSet ψ → bellProb ψ r = 1 / 2 ^ n) ∧
      (r + s ∉ stabSet ψ → bellProb ψ r = 0) := by
  obtain ⟨S, c, hc, hconj⟩ := BellSampling.Learn.conj_eq_sigmaZ ψ hψ
  have hnorm : ∑ x : Bits n, star (ψ x) * ψ x = 1 := stabilizer_norm_eq_one ψ hψ
  have h2 : ∀ a : ZMod 2, a + a = 0 := by decide
  have h_add_self : ∀ x : PStr n, x + x = 0 := by
    intro x
    ext i <;> exact h2 _
  refine ⟨zStr S, fun r => ?_⟩
  set t := r + zStr S
  have heq1 := BellSampling.Learn.eq_1 ψ S c hc hconj r
  have h_prob : bellProb ψ r = ‖∑ x, star (ψ x) * ((sigma t).mulVec ψ) x‖ ^ 2 / 2 ^ n := by
    rw [heq1]
    rcases BellSampling.Learn.sigma_mul r (zStr S) with hmul | hmul
    · rw [hmul]
    · rw [hmul]
      have hneg : (∑ x, star (ψ x) * ((-sigma t).mulVec ψ) x) =
          -(∑ x, star (ψ x) * ((sigma t).mulVec ψ) x) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun x _ => ?_
        simp [Matrix.neg_mulVec]
      rw [hneg, norm_neg]
  refine ⟨?_, ?_⟩
  · intro ht
    rcases ht with ⟨α, hα⟩
    rw [h_prob]
    have h_sum_α : (∑ x, star (ψ x) * ((sigma t).mulVec ψ) x) = α := by
      rw [hα]
      simp only [Pi.smul_apply, smul_eq_mul]
      have h_pull : (∑ x, star (ψ x) * (α * ψ x)) = α * ∑ x, star (ψ x) * ψ x := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        ring
      rw [h_pull, hnorm, mul_one]
    have h_sq_vec : ((sigma t * sigma t).mulVec ψ) = (α * α) • ψ := by
      rw [← Matrix.mulVec_mulVec, hα, Matrix.mulVec_smul, hα, smul_smul]
    have h_norm_α : ‖α‖ ^ 2 = 1 := by
      rcases BellSampling.Learn.sigma_mul t t with hsq | hsq
      · rw [h_add_self t, sigma_zero] at hsq
        rw [hsq, Matrix.one_mulVec] at h_sq_vec
        have h_dot : (∑ x, star (ψ x) * ((α * α) • ψ) x) = ∑ x, star (ψ x) * ψ x := by
          rw [← h_sq_vec]
        have h_lhs : (∑ x, star (ψ x) * ((α * α) • ψ) x) = α * α := by
          simp only [Pi.smul_apply, smul_eq_mul]
          have hp : (∑ x, star (ψ x) * (α * α * ψ x)) = (α * α) * ∑ x, star (ψ x) * ψ x := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun x _ => by ring
          rw [hp, hnorm, mul_one]
        have hα2 : α * α = 1 := by rw [← h_lhs, h_dot, hnorm]
        calc
          ‖α‖ ^ 2 = ‖α * α‖ := by rw [sq, ← norm_mul]
          _ = 1 := by rw [hα2, norm_one]
      · rw [h_add_self t, sigma_zero] at hsq
        rw [hsq, Matrix.neg_mulVec, Matrix.one_mulVec] at h_sq_vec
        have h_dot : (∑ x, star (ψ x) * ((α * α) • ψ) x) = ∑ x, star (ψ x) * (-ψ x) := by
          rw [← h_sq_vec]
          rfl
        have h_lhs : (∑ x, star (ψ x) * ((α * α) • ψ) x) = α * α := by
          simp only [Pi.smul_apply, smul_eq_mul]
          have hp : (∑ x, star (ψ x) * (α * α * ψ x)) = (α * α) * ∑ x, star (ψ x) * ψ x := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun x _ => by ring
          rw [hp, hnorm, mul_one]
        have h_rhs : (∑ x, star (ψ x) * (-ψ x)) = -1 := by
          simp_rw [mul_neg, Finset.sum_neg_distrib, hnorm]
        have hα2 : α * α = -1 := by rw [← h_lhs, h_dot, h_rhs]
        calc
          ‖α‖ ^ 2 = ‖α * α‖ := by rw [sq, ← norm_mul]
          _ = 1 := by rw [hα2, norm_neg, norm_one]
    rw [h_sum_α, h_norm_α]
  · intro ht
    rw [h_prob, BellSampling.Learn.expect_eq_zero_of_not_mem ψ hψ t ht]
    simp
