-- Prove2me | solution 1 for BayesGroupHard.VertexCover.eq_16
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T19:18:42.101364+00:00
-- url     : https://prove2.me/submissions/217a3774-7701-4ae0-af5f-cd7eeadaa5ed

import Mathlib
import Definitions.Def_bernoulliRelativeEntropy
import Definitions.Def_BayesGroupHard_VertexCover_Model

open Finset

namespace Aux_BayesGroupHard_VertexCover_eq_16

lemma kl_eq : BanditAlgorithm.bernoulliRelativeEntropy (998 / 1000) (4 / 10) =
    998 / 1000 * Real.log (499 / 200) - 2 / 1000 * Real.log 300 := by
  unfold BanditAlgorithm.bernoulliRelativeEntropy
  have e1 : (998 / 1000 : ℝ) / (4 / 10) = 499 / 200 := by norm_num
  have e2 : (1 - 998 / 1000 : ℝ) / (1 - 4 / 10) = (300 : ℝ)⁻¹ := by norm_num
  rw [e1, e2, Real.log_inv]
  ring

end Aux_BayesGroupHard_VertexCover_eq_16

open Aux_BayesGroupHard_VertexCover_eq_16 in
theorem solution (n : ℕ) (hn : 1 ≤ n) :
    ∑ C ∈ univ.filter (fun C : Finset (Fin n) => 998 / 1000 * (n : ℝ) < C.card),
          (4 / 10 : ℝ) ^ C.card * (6 / 10 : ℝ) ^ (n - C.card) ≤
        Real.exp (-((n : ℝ) * BanditAlgorithm.bernoulliRelativeEntropy (998 / 1000) (4 / 10))) ∧
      Real.exp (-((n : ℝ) * BanditAlgorithm.bernoulliRelativeEntropy (998 / 1000) (4 / 10))) <
        (41 / 100 : ℝ) ^ n := by
  rw [kl_eq]
  have hlogsplit : Real.log (1497 / 2) = Real.log (499 / 200) + Real.log 300 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h300 : (300 : ℝ) ^ n = Real.exp (n * Real.log 300) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  set L := Real.log (1497 / 2) with hL
  have hLpos : 0 < L := Real.log_pos (by norm_num)
  have hlam : ∀ c : ℕ, ((1497 / 2 : ℝ)) ^ c = Real.exp (c * L) := by
    intro c
    rw [Real.exp_nat_mul, hL, Real.exp_log (by norm_num)]
  constructor
  · have hterm : ∀ C ∈ univ.filter (fun C : Finset (Fin n) => 998 / 1000 * (n : ℝ) < C.card),
        (4 / 10 : ℝ) ^ C.card * (6 / 10 : ℝ) ^ (n - C.card) ≤
          Real.exp (-(998 / 1000 * n * L)) *
            (((1497 / 2 : ℝ) * (4 / 10)) ^ C.card * (6 / 10 : ℝ) ^ (n - C.card)) := by
      intro C hC
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC
      have h1 : 1 ≤ Real.exp (-(998 / 1000 * n * L)) * (1497 / 2 : ℝ) ^ C.card := by
        rw [hlam, ← Real.exp_add]
        apply Real.one_le_exp
        nlinarith
      have hpos : 0 ≤ (4 / 10 : ℝ) ^ C.card * (6 / 10 : ℝ) ^ (n - C.card) := by positivity
      calc (4 / 10 : ℝ) ^ C.card * (6 / 10 : ℝ) ^ (n - C.card)
          ≤ (Real.exp (-(998 / 1000 * n * L)) * (1497 / 2 : ℝ) ^ C.card) *
              ((4 / 10 : ℝ) ^ C.card * (6 / 10 : ℝ) ^ (n - C.card)) :=
            le_mul_of_one_le_left hpos h1
        _ = _ := by rw [mul_pow]; ring
    calc _ ≤ ∑ C ∈ univ.filter (fun C : Finset (Fin n) => 998 / 1000 * (n : ℝ) < C.card),
          Real.exp (-(998 / 1000 * n * L)) *
            (((1497 / 2 : ℝ) * (4 / 10)) ^ C.card * (6 / 10 : ℝ) ^ (n - C.card)) :=
          Finset.sum_le_sum hterm
      _ ≤ ∑ C : Finset (Fin n), Real.exp (-(998 / 1000 * n * L)) *
            (((1497 / 2 : ℝ) * (4 / 10)) ^ C.card * (6 / 10 : ℝ) ^ (n - C.card)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => by positivity)
      _ = Real.exp (-(998 / 1000 * n * L)) * (300 : ℝ) ^ n := by
          rw [← Finset.mul_sum, Fin.sum_pow_mul_eq_add_pow]
          norm_num
      _ = _ := by
          rw [h300, ← Real.exp_add, hlogsplit]
          congr 1
          ring
  · have hx : (1 : ℝ) + (50 : ℕ) * (459 / 20000) ≤ (1 + 459 / 20000) ^ 50 :=
      one_add_mul_le_pow (by norm_num) 50
    have hx' : (42950 / 20000 : ℝ) ≤ (20459 / 20000) ^ 50 := by norm_num at hx ⊢ <;> linarith
    have h9 : (42950 / 20000 : ℝ) ^ 9 ≤ ((20459 / 20000 : ℝ) ^ 50) ^ 9 :=
      pow_le_pow_left₀ (by norm_num) hx' 9
    have hr1 : (1 : ℝ) ≤ (20459 / 20000) ^ 49 := one_le_pow₀ (by norm_num)
    have hsplit : (499 / 200 : ℝ) ^ 499 * (41 / 100) ^ 500 =
        ((20459 / 20000 : ℝ) ^ 50) ^ 9 * (20459 / 20000) ^ 49 * (41 / 100) := by
      rw [← pow_mul, ← pow_add,
        pow_succ (41 / 100 : ℝ) 499, ← mul_assoc,
        ← mul_pow]
      norm_num
    have hc : (300 : ℝ) < (42950 / 20000 : ℝ) ^ 9 * (41 / 100) := by norm_num
    have hnum : (300 : ℝ) < (499 / 200 : ℝ) ^ 499 * (41 / 100) ^ 500 := by
      rw [hsplit]
      have h0 : (0 : ℝ) ≤ (42950 / 20000 : ℝ) ^ 9 := by positivity
      nlinarith
    have hlog := Real.log_lt_log (by norm_num) hnum
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hlog
    have h41 : (41 / 100 : ℝ) ^ n = Real.exp (n * Real.log (41 / 100)) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    rw [h41, Real.exp_lt_exp]
    have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hk : -(998 / 1000 * Real.log (499 / 200) - 2 / 1000 * Real.log 300) <
        Real.log (41 / 100) := by
      push_cast at hlog
      linarith
    have := mul_lt_mul_of_pos_left hk hn'
    linarith
