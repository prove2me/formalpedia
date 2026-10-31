-- Prove2me | solution 1 for BayesGroupHard.VertexCover.theorem_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T23:59:13.87992+00:00
-- url     : https://prove2.me/submissions/49feeb98-8302-4a8f-aa70-e34eec57d87b

import Mathlib
import Definitions.Def_bernoulliRelativeEntropy
import Definitions.Def_BayesGroupHard_VertexCover_Model

open Finset

namespace BayesGroupHard.VertexCover

theorem bvc_theorem_7 (n : ℕ) (p α : ℝ) (hp : 0 ≤ p) (hpα : p ≤ α) (hα : α ≤ 1) :
    ∑ C ∈ univ.filter (fun C : Finset (Fin n) => α * (n : ℝ) ≤ C.card),
        p ^ C.card * (1 - p) ^ (n - C.card) ≤
      Real.exp (-((n : ℝ) * BanditAlgorithm.bernoulliRelativeEntropy α p)) := by
  have hp1 : 0 ≤ 1 - p := by linarith
  have htot : ∑ C : Finset (Fin n), p ^ C.card * (1 - p) ^ (n - C.card) = 1 := by
    rw [Fin.sum_pow_mul_eq_add_pow]; simp
  have hle1 : ∑ C ∈ univ.filter (fun C : Finset (Fin n) => α * (n : ℝ) ≤ C.card),
      p ^ C.card * (1 - p) ^ (n - C.card) ≤ 1 := by
    exact (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun _ _ _ => by positivity)).trans htot.le
  rcases eq_or_lt_of_le hpα with hpa | hpa
  · -- `α = p`
    subst hpa
    have hKL : BanditAlgorithm.bernoulliRelativeEntropy p p = 0 := by
      unfold BanditAlgorithm.bernoulliRelativeEntropy
      by_cases h0 : p = 0
      · simp [h0]
      by_cases h1 : 1 - p = 0
      · simp [h1]
      rw [div_self h0, div_self h1]; simp
    rw [hKL]; simpa using hle1
  rcases eq_or_lt_of_le hp with hp0 | hp0
  · -- `p = 0`
    subst hp0
    have hKL : BanditAlgorithm.bernoulliRelativeEntropy α 0 ≤ 0 := by
      unfold BanditAlgorithm.bernoulliRelativeEntropy
      simp only [div_zero, Real.log_zero, mul_zero, zero_add, sub_zero, div_one]
      exact mul_nonpos_of_nonneg_of_nonpos (by linarith)
        (Real.log_nonpos (by linarith) (by linarith))
    have : 1 ≤ Real.exp (-((n : ℝ) * BanditAlgorithm.bernoulliRelativeEntropy α 0)) := by
      apply Real.one_le_exp
      have : (0 : ℝ) ≤ n := by positivity
      nlinarith
    linarith
  rcases eq_or_lt_of_le hα with ha1 | ha1
  · -- `α = 1`
    subst ha1
    have hfil : univ.filter (fun C : Finset (Fin n) => 1 * (n : ℝ) ≤ C.card) = {univ} := by
      ext C
      simp only [mem_filter, mem_univ, true_and, one_mul, mem_singleton]
      constructor
      · intro h
        apply Finset.eq_univ_of_card
        have h1 : n ≤ C.card := by exact_mod_cast h
        have h2 : C.card ≤ n := card_le_univ C |>.trans (by simp)
        simp; omega
      · rintro rfl; simp
    rw [hfil, sum_singleton, card_univ, Fintype.card_fin, Nat.sub_self, pow_zero, mul_one]
    unfold BanditAlgorithm.bernoulliRelativeEntropy
    simp only [sub_self, zero_div, Real.log_zero, mul_zero, add_zero, one_mul, one_div,
      Real.log_inv]
    rw [show -((n : ℝ) * -Real.log p) = n * Real.log p by ring, Real.exp_nat_mul,
      Real.exp_log hp0]
  · -- `0 < p < α < 1`: the Chernoff bound
    set t : ℝ := α * (1 - p) / (p * (1 - α)) with ht
    have hα0 : 0 < 1 - α := by linarith
    have hp1' : 0 < 1 - p := by linarith
    have ht0 : 0 < t := div_pos (mul_pos (by linarith) hp1') (mul_pos hp0 hα0)
    have ht1 : 1 ≤ t := by
      rw [ht, le_div_iff₀ (by positivity)]
      nlinarith
    have hstep : ∑ C ∈ univ.filter (fun C : Finset (Fin n) => α * (n : ℝ) ≤ C.card),
        p ^ C.card * (1 - p) ^ (n - C.card) ≤
        (∑ C : Finset (Fin n), (t * p) ^ C.card * (1 - p) ^ (n - C.card)) / t ^ (α * n) := by
      rw [le_div_iff₀ (Real.rpow_pos_of_pos ht0 _), sum_mul]
      calc _ ≤ ∑ C ∈ univ.filter (fun C : Finset (Fin n) => α * (n : ℝ) ≤ C.card),
            (t * p) ^ C.card * (1 - p) ^ (n - C.card) := by
            apply sum_le_sum
            intro C hC
            simp only [mem_filter, mem_univ, true_and] at hC
            have h1 : t ^ (α * n) ≤ t ^ C.card := by
              rw [← Real.rpow_natCast]
              exact Real.rpow_le_rpow_of_exponent_le ht1 hC
            rw [mul_pow]
            have : 0 ≤ p ^ C.card * (1 - p) ^ (n - C.card) := by positivity
            nlinarith
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
    refine hstep.trans (le_of_eq ?_)
    rw [Fin.sum_pow_mul_eq_add_pow]
    have hsum : t * p + (1 - p) = (1 - p) / (1 - α) := by
      rw [ht]; field_simp; ring
    have hlogt : Real.log t = Real.log (α / p) + Real.log ((1 - p) / (1 - α)) := by
      have hαp : 0 < α / p := div_pos (by linarith) hp0
      rw [← Real.log_mul hαp.ne' (div_pos hp1' hα0).ne']
      congr 1
      rw [ht]; field_simp
    rw [hsum, ← Real.exp_log (div_pos hp1' hα0), ← Real.exp_nat_mul,
      Real.rpow_def_of_pos ht0, ← Real.exp_sub, hlogt]
    congr 1
    unfold BanditAlgorithm.bernoulliRelativeEntropy
    rw [Real.log_div hα0.ne' hp1'.ne', Real.log_div hp1'.ne' hα0.ne']
    ring

end BayesGroupHard.VertexCover

open BayesGroupHard.VertexCover in
theorem solution (n : ℕ) (p α : ℝ) (hp : 0 ≤ p) (hpα : p ≤ α) (hα : α ≤ 1) :
    ∑ C ∈ univ.filter (fun C : Finset (Fin n) => α * (n : ℝ) ≤ C.card),
        p ^ C.card * (1 - p) ^ (n - C.card) ≤
      Real.exp (-((n : ℝ) * BanditAlgorithm.bernoulliRelativeEntropy α p)) :=
  BayesGroupHard.VertexCover.bvc_theorem_7 n p α hp hpα hα
