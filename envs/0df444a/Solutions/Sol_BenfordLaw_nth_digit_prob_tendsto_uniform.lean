-- Prove2me | solution 1 for BenfordLaw.nth_digit_prob_tendsto_uniform
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T02:49:12.113481+00:00
-- url     : https://prove2.me/submissions/00bbe165-142f-4c5d-8eb5-72e46085811a

import Mathlib
import Definitions.Def_BenfordLaw_Defs
open BenfordLaw

lemma log_one_add_inv_bounds (m : ℝ) (hm : 0 < m) :
    1 / (m + 1) ≤ Real.log (1 + 1 / m) ∧ Real.log (1 + 1 / m) ≤ 1 / m := by
  have hpos : 0 < 1 + 1 / m := by positivity
  constructor
  · have := Real.one_sub_inv_le_log_of_pos hpos
    have e : 1 - (1 + 1 / m)⁻¹ = 1 / (m + 1) := by field_simp; ring
    linarith
  · have := Real.log_le_sub_one_of_pos hpos
    linarith

lemma telescope_Ico (f : ℕ → ℝ) (a : ℕ) : ∀ m, a ≤ m →
    ∑ k ∈ Finset.Ico a m, (f (k + 1) - f k) = f m - f a := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => simp
  | succ m hm ih => rw [Finset.sum_Ico_succ_top hm, ih]; ring

lemma nth_digit_sum_bound (d : ℕ) (hd : d ≤ 9) (K : ℕ) (hK : 1 ≤ K) :
    |∑ k ∈ Finset.Ico K (10 * K), Real.logb 10 (1 + 1 / (10 * (k : ℝ) + d)) - 1 / 10| ≤ 1 / K := by
  have hL : 1 < Real.log 10 := by
    have := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    linarith
  have hL0 : 0 < Real.log 10 := by linarith
  set L := Real.log 10
  -- the telescoping comparison sum
  have hb : ∑ k ∈ Finset.Ico K (10 * K), Real.log (1 + 1 / (k : ℝ)) / (10 * L) = 1 / 10 := by
    have : ∀ k ∈ Finset.Ico K (10 * K), Real.log (1 + 1 / (k : ℝ)) / (10 * L) =
        Real.log ((k + 1 : ℕ) : ℝ) / (10 * L) - Real.log (k : ℝ) / (10 * L) := by
      intro k hk
      rw [Finset.mem_Ico] at hk
      have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      rw [← sub_div, ← Real.log_div (by positivity) hk0.ne']
      congr 2
      push_cast
      field_simp
    rw [Finset.sum_congr rfl this, telescope_Ico (fun k => Real.log (k : ℝ) / (10 * L)) K (10 * K)
      (by omega)]
    have hK0 : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
    rw [← sub_div, ← Real.log_div (by positivity) hK0.ne']
    push_cast
    rw [show (10 * (K : ℝ)) / K = 10 by field_simp]
    field_simp
    rfl
  -- termwise bound
  have hterm : ∀ k ∈ Finset.Ico K (10 * K),
      |Real.logb 10 (1 + 1 / (10 * (k : ℝ) + d)) - Real.log (1 + 1 / (k : ℝ)) / (10 * L)| ≤
        (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) / (10 * L) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hd0 : (0 : ℝ) ≤ d := by positivity
    obtain ⟨a1, a2⟩ := log_one_add_inv_bounds (10 * (k : ℝ) + d) (by positivity)
    obtain ⟨b1, b2⟩ := log_one_add_inv_bounds (k : ℝ) hk0
    have hd9 : (d : ℝ) ≤ 9 := by exact_mod_cast hd
    set A := Real.log (1 + 1 / (10 * (k : ℝ) + d))
    set B := Real.log (1 + 1 / (k : ℝ))
    have hA1 : 10 * A ≤ 1 / k := by
      have e1 : 1 / (10 * (k : ℝ) + d) ≤ 1 / (10 * k) := by
        apply one_div_le_one_div_of_le (by positivity); linarith
      have e2 : 10 * (1 / (10 * (k : ℝ))) = 1 / k := by field_simp
      linarith
    have hA2 : 1 / ((k : ℝ) + 1) ≤ 10 * A := by
      have e1 : 1 / (10 * (k : ℝ) + 10) ≤ 1 / (10 * (k : ℝ) + d + 1) := by
        apply one_div_le_one_div_of_le (by positivity); linarith
      have e2 : 10 * (1 / (10 * (k : ℝ) + 10)) = 1 / ((k : ℝ) + 1) := by field_simp
      linarith
    have expr : Real.logb 10 (1 + 1 / (10 * (k : ℝ) + d)) - B / (10 * L) = (10 * A - B) / (10 * L) := by
      show A / L - B / (10 * L) = _
      field_simp
    rw [expr, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 10 * L)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    push_cast
    rw [abs_le]
    constructor <;> linarith
  have hsum := Finset.abs_sum_le_sum_abs
    (fun k : ℕ => Real.logb 10 (1 + 1 / (10 * (k : ℝ) + d)) - Real.log (1 + 1 / (k : ℝ)) / (10 * L))
    (Finset.Ico K (10 * K))
  rw [Finset.sum_sub_distrib, hb] at hsum
  refine le_trans hsum (le_trans (Finset.sum_le_sum hterm) ?_)
  have htel : ∑ k ∈ Finset.Ico K (10 * K), (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) / (10 * L) =
      (1 / (K : ℝ) - 1 / ((10 * K : ℕ) : ℝ)) / (10 * L) := by
    have := telescope_Ico (fun k => -(1 / (k : ℝ)) / (10 * L)) K (10 * K) (by omega)
    rw [show (1 / (K : ℝ) - 1 / ((10 * K : ℕ) : ℝ)) / (10 * L) =
      -(1 / ((10 * K : ℕ) : ℝ)) / (10 * L) - -(1 / (K : ℝ)) / (10 * L) by ring, ← this]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [htel]
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have h1 : 0 ≤ 1 / ((10 * K : ℕ) : ℝ) := by positivity
  rw [div_le_iff₀ (by positivity)]
  have : 1 / (K : ℝ) ≤ 1 / K * (10 * L) := by
    have : (0 : ℝ) < 1 / K := by positivity
    nlinarith
  linarith

theorem solution (d : ℕ) (hd : d ≤ 9) :
    Filter.Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.Ico (10 ^ (n - 2) : ℕ) (10 ^ (n - 1)),
        Real.logb 10 (1 + 1 / (10 * (k : ℝ) + d)))
      Filter.atTop (nhds (1 / 10)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Filter.Tendsto (fun n : ℕ => (1 / 10 : ℝ) ^ (n - 2)) Filter.atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
      (Filter.tendsto_sub_atTop_nat 2)
  refine squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg _) ?_ hlim
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  have hpow : 10 ^ (n - 1) = 10 * 10 ^ (n - 2) := by
    rw [← pow_succ']; congr 1; omega
  rw [hpow, Real.norm_eq_abs]
  refine le_trans (nth_digit_sum_bound d hd _ (Nat.one_le_pow _ _ (by norm_num))) (le_of_eq ?_)
  push_cast
  rw [one_div_pow, one_div]
