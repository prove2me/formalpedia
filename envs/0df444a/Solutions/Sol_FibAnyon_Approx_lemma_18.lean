-- Prove2me | solution 1 for FibAnyon.Approx.lemma_18
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T22:24:04.975122+00:00
-- url     : https://prove2.me/submissions/7439f59f-96fe-4c8e-a40e-f47450c604cf

import Mathlib
import Definitions.Def_FibAnyon_Approx_Model

noncomputable section

open FibAnyon.Approx

private lemma sqrt5_sq : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)

private lemma sqrt5_bounds :
    (2236 : ℝ) / 1000 < Real.sqrt 5 ∧ Real.sqrt 5 < (2237 : ℝ) / 1000 := by
  constructor
  · rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2236 / 1000)]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  · rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2237 / 1000)]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

private lemma tau_sq_eq : tau ^ 2 = 1 - tau := by
  unfold tau
  nlinarith [sqrt5_sq]

private lemma gold_sq_eq : gold ^ 2 = gold + 1 := by
  unfold gold
  nlinarith [sqrt5_sq]

private lemma gold_mul_tau : gold * tau = 1 := by
  unfold gold tau
  nlinarith [sqrt5_sq]

private lemma fib_sub_tau (k : ℕ) :
    (Nat.fib k : ℝ) - (Nat.fib (k + 1) : ℝ) * tau = (-1 : ℝ) ^ (k + 1) * tau ^ (k + 1) := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    have h_fib : (Nat.fib (k + 2) : ℝ) = (Nat.fib k : ℝ) + (Nat.fib (k + 1) : ℝ) := by
      exact_mod_cast Nat.fib_add_two
    calc (Nat.fib (k + 1) : ℝ) - (Nat.fib (k + 2) : ℝ) * tau
      _ = (Nat.fib (k + 1) : ℝ) * (1 - tau) - (Nat.fib k : ℝ) * tau := by rw [h_fib]; ring
      _ = (Nat.fib (k + 1) : ℝ) * tau ^ 2 - (Nat.fib k : ℝ) * tau := by rw [← tau_sq_eq]
      _ = -tau * ((Nat.fib k : ℝ) - (Nat.fib (k + 1) : ℝ) * tau) := by ring
      _ = -tau * ((-1 : ℝ) ^ (k + 1) * tau ^ (k + 1)) := by rw [ih]
      _ = (-1 : ℝ) ^ (k + 2) * tau ^ (k + 2) := by ring

private lemma fib_add_gold (k : ℕ) :
    (Nat.fib (k + 1) : ℝ) * gold + (Nat.fib k : ℝ) = gold ^ (k + 1) := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    have h_fib : (Nat.fib (k + 2) : ℝ) = (Nat.fib k : ℝ) + (Nat.fib (k + 1) : ℝ) := by
      exact_mod_cast Nat.fib_add_two
    calc (Nat.fib (k + 2) : ℝ) * gold + (Nat.fib (k + 1) : ℝ)
      _ = ((Nat.fib k : ℝ) + (Nat.fib (k + 1) : ℝ)) * gold + (Nat.fib (k + 1) : ℝ) := by
        rw [h_fib]
      _ = (Nat.fib (k + 1) : ℝ) * (gold + 1) + (Nat.fib k : ℝ) * gold := by ring
      _ = (Nat.fib (k + 1) : ℝ) * gold ^ 2 + (Nat.fib k : ℝ) * gold := by rw [← gold_sq_eq]
      _ = ((Nat.fib (k + 1) : ℝ) * gold + (Nat.fib k : ℝ)) * gold := by ring
      _ = gold ^ (k + 1) * gold := by rw [ih]
      _ = gold ^ (k + 2) := by ring

private lemma fib_cassini (k : ℕ) :
    (Nat.fib (k + 2) : ℤ) * (Nat.fib k : ℤ) - (Nat.fib (k + 1) : ℤ) ^ 2 = (-1 : ℤ) ^ (k + 1) := by
  induction k with
  | zero =>
    decide
  | succ k ih =>
    have h1 : (Nat.fib (k + 2) : ℤ) = (Nat.fib k : ℤ) + (Nat.fib (k + 1) : ℤ) := by
      exact_mod_cast Nat.fib_add_two
    have h2 : (Nat.fib (k + 3) : ℤ) = (Nat.fib (k + 1) : ℤ) + (Nat.fib (k + 2) : ℤ) := by
      exact_mod_cast @Nat.fib_add_two (k + 1)
    have h_step :
        (Nat.fib (k + 3) : ℤ) * (Nat.fib (k + 1) : ℤ) - (Nat.fib (k + 2) : ℤ) ^ 2 =
          -((Nat.fib (k + 2) : ℤ) * (Nat.fib k : ℤ) - (Nat.fib (k + 1) : ℤ) ^ 2) := by
      linear_combination (Nat.fib (k + 1) : ℤ) * h2 - (Nat.fib (k + 2) : ℤ) * h1
    rw [h_step, ih]
    ring

private lemma fib_tau_bound (m : ℕ) :
    1 ≤ (Nat.fib (m + 3) : ℝ) * (2 * tau ^ (m + 1) - tau ^ (m + 3) - 2 * tau ^ (2 * m + 3)) := by
  have h_tau_sq := tau_sq_eq
  have h_gold_sq := gold_sq_eq
  have h_tau_cube : tau ^ 3 = 2 * tau - 1 := by linear_combination (tau - 1) * h_tau_sq
  have h_tau_four : tau ^ 4 = 2 - 3 * tau := by linear_combination (tau ^ 2 - tau + 2) * h_tau_sq
  have h_gold_cube : gold ^ 3 = 2 * gold + 1 := by linear_combination (gold + 1) * h_gold_sq
  have h_s5 := sqrt5_bounds
  have h_tau_pos : 0 < tau := by unfold tau; linarith [h_s5.1]
  have h_tau_lt_one : tau < 1 := by unfold tau; linarith [h_s5.2]
  have h_factor :
      2 * tau ^ (m + 1) - tau ^ (m + 3) - 2 * tau ^ (2 * m + 3) =
        tau ^ m * (1 - 2 * tau ^ (m + 3)) := by
    have h_sub : 2 * tau ^ (m + 1) - tau ^ (m + 3) = tau ^ m := by
      calc 2 * tau ^ (m + 1) - tau ^ (m + 3)
        _ = tau ^ m * (2 * tau - tau ^ 3) := by ring
        _ = tau ^ m * 1 := by rw [h_tau_cube]; ring
        _ = tau ^ m := by ring
    linear_combination h_sub
  rw [h_factor]
  rcases m with _ | k
  · have h_fib3 : (Nat.fib 3 : ℝ) = 2 := by norm_num
    rw [h_fib3, pow_zero, one_mul, zero_add, h_tau_cube]
    unfold tau
    linarith [h_s5.2]
  · set j := k + 1
    have hj : 1 ≤ j := Nat.succ_le_succ (Nat.zero_le k)
    have h_binet :
        (Nat.fib (j + 3) : ℝ) * (gold + tau) =
          gold ^ (j + 3) - (-1 : ℝ) ^ (j + 3) * tau ^ (j + 3) := by
      have h1 := fib_add_gold (j + 2)
      have h2 := fib_sub_tau (j + 2)
      linear_combination h1 - h2
    have h_gt_Cancel : gold ^ (j + 3) * tau ^ j = gold ^ 3 := by
      calc gold ^ (j + 3) * tau ^ j
        _ = gold ^ 3 * (gold ^ j * tau ^ j) := by ring
        _ = gold ^ 3 * (gold * tau) ^ j := by rw [← mul_pow]
        _ = gold ^ 3 := by rw [gold_mul_tau, one_pow, mul_one]
    have h_binet_scaled :
        (Nat.fib (j + 3) : ℝ) * tau ^ j * (gold + tau) =
          gold ^ 3 - (-1 : ℝ) ^ (j + 3) * tau ^ (2 * j + 3) := by
      calc (Nat.fib (j + 3) : ℝ) * tau ^ j * (gold + tau)
        _ = (Nat.fib (j + 3) : ℝ) * (gold + tau) * tau ^ j := by ring
        _ = (gold ^ (j + 3) - (-1 : ℝ) ^ (j + 3) * tau ^ (j + 3)) * tau ^ j := by rw [h_binet]
        _ = gold ^ (j + 3) * tau ^ j - (-1 : ℝ) ^ (j + 3) * tau ^ (2 * j + 3) := by ring
        _ = gold ^ 3 - (-1 : ℝ) ^ (j + 3) * tau ^ (2 * j + 3) := by rw [h_gt_Cancel]
    have h_pow1 : tau ^ (j + 3) ≤ tau ^ 4 :=
      pow_le_pow_of_le_one (le_of_lt h_tau_pos) (le_of_lt h_tau_lt_one) (by omega)
    have h_pow2 : tau ^ (2 * j + 3) ≤ tau ^ 4 :=
      pow_le_pow_of_le_one (le_of_lt h_tau_pos) (le_of_lt h_tau_lt_one) (by omega)
    have h_neg_pow : (-1 : ℝ) ^ (j + 3) * tau ^ (2 * j + 3) ≤ tau ^ 4 := by
      have h_abs :
          (-1 : ℝ) ^ (j + 3) * tau ^ (2 * j + 3) ≤
            |(-1 : ℝ) ^ (j + 3) * tau ^ (2 * j + 3)| := le_abs_self _
      rw [abs_mul, abs_neg_one_pow, one_mul,
        abs_of_nonneg (pow_nonneg (le_of_lt h_tau_pos) _)] at h_abs
      exact le_trans h_abs h_pow2
    have h_A_ge : gold ^ 3 - tau ^ 4 ≤ (Nat.fib (j + 3) : ℝ) * tau ^ j * (gold + tau) := by
      linarith [h_binet_scaled, h_neg_pow]
    have h_B_ge : 1 - 2 * tau ^ 4 ≤ 1 - 2 * tau ^ (j + 3) := by linarith [h_pow1]
    have h_B_pos : 0 ≤ 1 - 2 * tau ^ 4 := by
      rw [h_tau_four]; unfold tau; linarith [h_s5.1]
    have h_A_pos : 0 ≤ (Nat.fib (j + 3) : ℝ) * tau ^ j * (gold + tau) := by
      have : 0 ≤ gold ^ 3 - tau ^ 4 := by
        rw [h_gold_cube, h_tau_four]; unfold gold tau; linarith [h_s5.1]
      linarith
    have h_prod_ge :
        (gold ^ 3 - tau ^ 4) * (1 - 2 * tau ^ 4) ≤
          ((Nat.fib (j + 3) : ℝ) * tau ^ j * (gold + tau)) * (1 - 2 * tau ^ (j + 3)) :=
      mul_le_mul h_A_ge h_B_ge h_B_pos h_A_pos
    have h_num_ge : gold + tau ≤ (gold ^ 3 - tau ^ 4) * (1 - 2 * tau ^ 4) := by
      rw [h_gold_cube, h_tau_four]
      unfold gold tau
      nlinarith [h_s5.1, h_s5.2]
    have h_gt_pos : 0 < gold + tau := by unfold gold tau; linarith [h_s5.1]
    nlinarith

theorem solution (x : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    let z := approxReal x n
    |x - ((z.1 : ℝ) + (z.2 : ℝ) * tau)| ≤
        tau^(n-1) * (1 - tau^n) ∧
      |(z.2 : ℝ)| ≤ gold^n := by
  dsimp only
  let p : ℤ := Nat.fib n
  let q : ℤ := Nat.fib (n + 1)
  let uF : ℤ := (-1 : ℤ) ^ (n + 1) * Nat.fib n
  let vF : ℤ := (-1 : ℤ) ^ n * Nat.fib (n - 1)
  let c : ℤ := round (x * (q : ℝ))
  let z0 : ℤ := round (((c * uF : ℤ) : ℝ) / (q : ℝ))
  let a : ℤ := c * vF + p * z0
  let b : ℤ := c * uF - q * z0
  change |x - ((a : ℝ) + (b : ℝ) * tau)| ≤ tau ^ (n - 1) * (1 - tau ^ n) ∧ |(b : ℝ)| ≤ gold ^ n
  have h_s5 := sqrt5_bounds
  have h_tau_pos : 0 < tau := by unfold tau; linarith [h_s5.1]
  have h_gold_gt_one : 1 < gold := by unfold gold; linarith [h_s5.1]
  have hq_pos_nat : 0 < Nat.fib (n + 1) := Nat.fib_pos.mpr (by omega)
  have hq_pos : 0 < (q : ℝ) := by dsimp [q]; exact_mod_cast hq_pos_nat
  have hq_ne : (q : ℝ) ≠ 0 := ne_of_gt hq_pos
  have h_round_z : |((c * uF : ℤ) : ℝ) / (q : ℝ) - (z0 : ℝ)| ≤ 1 / 2 :=
    abs_sub_round (((c * uF : ℤ) : ℝ) / (q : ℝ))
  have hb_eq : (b : ℝ) = (q : ℝ) * (((c * uF : ℤ) : ℝ) / (q : ℝ) - (z0 : ℝ)) := by
    dsimp [b]
    push_cast
    rw [mul_sub, mul_div_cancel₀ _ hq_ne]
  have hb_le_half_q : |(b : ℝ)| ≤ (q : ℝ) / 2 := by
    rw [hb_eq, abs_mul, abs_of_pos hq_pos]
    linarith [mul_le_mul_of_nonneg_left h_round_z (le_of_lt hq_pos)]
  have hb_le_gold : |(b : ℝ)| ≤ gold ^ n := by
    have h_fg := fib_add_gold (n - 1)
    have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
    have hn2 : n - 1 + 2 = n + 1 := by omega
    rw [hn1] at h_fg
    have h_fib_add : (q : ℝ) = (Nat.fib (n - 1) : ℝ) + (Nat.fib n : ℝ) := by
      dsimp [q]
      have h_nat : Nat.fib (n + 1) = Nat.fib (n - 1) + Nat.fib n := by
        have h_two := @Nat.fib_add_two (n - 1)
        rwa [hn1, hn2] at h_two
      exact_mod_cast h_nat
    have h_fib_nonneg : 0 ≤ (Nat.fib n : ℝ) := Nat.cast_nonneg _
    have hq_le_gold : (q : ℝ) ≤ gold ^ n := by
      nlinarith [h_fg, h_fib_add, h_gold_gt_one, h_fib_nonneg]
    linarith
  have h_cassini_int : q * vF + p * uF = 1 := by
    have hc := fib_cassini (n - 1)
    have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
    have hn2 : n - 1 + 2 = n + 1 := by omega
    rw [hn1, hn2] at hc
    have h_alg :
        q * vF + p * uF =
          (-1 : ℤ) ^ n * ((Nat.fib (n + 1) : ℤ) * (Nat.fib (n - 1) : ℤ) - (Nat.fib n : ℤ) ^ 2) := by
      dsimp [q, p, uF, vF]
      ring
    rw [h_alg, hc, ← mul_pow]
    norm_num
  have h_cassini_real : (q : ℝ) * (vF : ℝ) + (p : ℝ) * (uF : ℝ) = 1 := by
    exact_mod_cast h_cassini_int
  have h_decomp :
      (q : ℝ) * (x - ((a : ℝ) + (b : ℝ) * tau)) =
        (x * (q : ℝ) - (c : ℝ)) + (b : ℝ) * ((p : ℝ) - (q : ℝ) * tau) := by
    dsimp [a, b]
    push_cast
    linear_combination -(c : ℝ) * h_cassini_real
  have h_round_c : |x * (q : ℝ) - (c : ℝ)| ≤ 1 / 2 := abs_sub_round (x * (q : ℝ))
  have h_pq_tau : |(p : ℝ) - (q : ℝ) * tau| = tau ^ (n + 1) := by
    have h_eq : (p : ℝ) - (q : ℝ) * tau = (-1 : ℝ) ^ (n + 1) * tau ^ (n + 1) := by
      dsimp [p, q]
      exact fib_sub_tau n
    rw [h_eq, abs_mul, abs_neg_one_pow, one_mul,
      abs_of_nonneg (pow_nonneg (le_of_lt h_tau_pos) _)]
  have h_abs_decomp :
      (q : ℝ) * |x - ((a : ℝ) + (b : ℝ) * tau)| ≤ 1 / 2 + (q : ℝ) / 2 * tau ^ (n + 1) := by
    have h1 :
        |(q : ℝ) * (x - ((a : ℝ) + (b : ℝ) * tau))| ≤
          |x * (q : ℝ) - (c : ℝ)| + |(b : ℝ) * ((p : ℝ) - (q : ℝ) * tau)| := by
      rw [h_decomp]
      exact abs_add_le _ _
    rw [abs_mul, abs_of_pos hq_pos, abs_mul, h_pq_tau] at h1
    have h2 :
        |(b : ℝ)| * tau ^ (n + 1) ≤ (q : ℝ) / 2 * tau ^ (n + 1) :=
      mul_le_mul_of_nonneg_right hb_le_half_q (pow_nonneg (le_of_lt h_tau_pos) _)
    linarith
  have h_rhs_bound :
      1 / 2 + (q : ℝ) / 2 * tau ^ (n + 1) ≤ (q : ℝ) * (tau ^ (n - 1) * (1 - tau ^ n)) := by
    set m := n - 2
    have hm : n = m + 2 := by omega
    have hm1 : n - 1 = m + 1 := by omega
    have hm3 : n + 1 = m + 3 := by omega
    have h_ft := fib_tau_bound m
    have hq_m : (q : ℝ) = (Nat.fib (m + 3) : ℝ) := by
      dsimp [q]
      rw [hm3]
      norm_cast
    rw [hq_m, hm1, hm3, hm]
    have h_alg :
        (Nat.fib (m + 3) : ℝ) * (tau ^ (m + 1) * (1 - tau ^ (m + 2))) -
            (1 / 2 + (Nat.fib (m + 3) : ℝ) / 2 * tau ^ (m + 3)) =
          ((Nat.fib (m + 3) : ℝ) * (2 * tau ^ (m + 1) - tau ^ (m + 3) - 2 * tau ^ (2 * m + 3)) - 1) / 2 := by
      ring
    linarith
  have h_err_bound : |x - ((a : ℝ) + (b : ℝ) * tau)| ≤ tau ^ (n - 1) * (1 - tau ^ n) := by
    have h_comb := le_trans h_abs_decomp h_rhs_bound
    exact le_of_mul_le_mul_left h_comb hq_pos
  exact ⟨h_err_bound, hb_le_gold⟩
