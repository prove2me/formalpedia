-- Prove2me | solution 1 for AvramDividend.Classical.bv_rare_grid_exponential_limit_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T23:49:28.261887+00:00
-- url     : https://prove2.me/submissions/b1a3b9b1-b96b-4353-ac83-35f547f8068a

import Mathlib

open Filter Topology
open scoped NNReal

theorem solution (r : ℝ) :
    Tendsto (fun n : ℕ =>
      (n : ℝ) * (1 - Real.exp (-(r / (n : ℝ)))))
      atTop (nhds r) := by
  have hbound : ∀ᶠ n : ℕ in atTop,
      |(n : ℝ) * (1 - Real.exp (-(r / (n : ℝ)))) - r| ≤ r ^ 2 / (n : ℝ) := by
    filter_upwards [eventually_ge_atTop (Nat.ceil |r| + 1)] with n hn
    have hn1 : (1 : ℝ) ≤ n := by
      have : (1 : ℕ) ≤ n := le_trans (Nat.le_add_left 1 _) hn
      exact_mod_cast this
    have hnpos : (0 : ℝ) < n := lt_of_lt_of_le one_pos hn1
    have hrn : |r| ≤ n := by
      have h1 : |r| ≤ (Nat.ceil |r| : ℝ) := Nat.le_ceil _
      have h2 : ((Nat.ceil |r| : ℕ) : ℝ) ≤ n := by
        exact_mod_cast le_trans (Nat.le_succ _) hn
      linarith
    have hx : |(-(r / (n : ℝ)))| ≤ 1 := by
      rw [abs_neg, abs_div, abs_of_pos hnpos, div_le_one hnpos]; exact hrn
    have h := Real.abs_exp_sub_one_sub_id_le hx
    have heq : (n : ℝ) * (1 - Real.exp (-(r / (n : ℝ)))) - r =
        -((n : ℝ) * (Real.exp (-(r / (n : ℝ))) - 1 - (-(r / (n : ℝ))))) := by
      field_simp; ring
    rw [heq, abs_neg, abs_mul, abs_of_pos hnpos]
    calc (n : ℝ) * |Real.exp (-(r / (n : ℝ))) - 1 - (-(r / (n : ℝ)))|
        ≤ (n : ℝ) * (-(r / (n : ℝ))) ^ 2 := mul_le_mul_of_nonneg_left h hnpos.le
      _ = r ^ 2 / (n : ℝ) := by field_simp
  have hlim : Tendsto (fun n : ℕ => r ^ 2 / (n : ℝ)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall (fun n => norm_nonneg _)) ?_ hlim
  filter_upwards [hbound] with n hn
  rw [Real.norm_eq_abs]; exact hn
