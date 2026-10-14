-- Prove2me | solution 1 for ClassicalSecretary.tendsto_optimalProb
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-12T16:05:10.611476+00:00
-- url     : https://prove2.me/submissions/babf4c12-177c-4c20-95e2-ef051e29d80e

import Mathlib
import Definitions.Def_ClassicalSecretary_Model
import Theorems.Thm_ClassicalSecretary_successProb_cutoffRule_one
import Theorems.Thm_ClassicalSecretary_successProb_cutoffRule
import Theorems.Thm_ClassicalSecretary_exists_optimal_cutoffRule
import Theorems.Thm_ClassicalSecretary_exp_neg_one_le_optimalProb

set_option autoImplicit false

open Finset Filter Topology

namespace ClassicalSecretary.SecAn

/-! ### Elementary logarithm inequalities -/

/-- `log t ≤ (t - t⁻¹)/2` for `t ≥ 1` (i.e. `u ≤ sinh u` for `u = log t ≥ 0`). -/
lemma log_le_half_sub_inv {t : ℝ} (ht : 1 ≤ t) : Real.log t ≤ (t - t⁻¹) / 2 := by
  have h0 : 0 < t := by linarith
  rw [← Real.sinh_log h0]
  exact Real.self_le_sinh_iff.mpr (Real.log_nonneg ht)

/-- `(t - t⁻¹)/2 ≤ log t` for `0 < t ≤ 1`. -/
lemma half_sub_inv_le_log {t : ℝ} (h0 : 0 < t) (ht : t ≤ 1) : (t - t⁻¹) / 2 ≤ Real.log t := by
  rw [← Real.sinh_log h0]
  exact Real.sinh_le_self_iff.mpr (Real.log_nonpos h0.le ht)

/-- `2 (y - 1)/(y + 1) ≤ log y` for `y ≥ 1` (first term of the series of `log (1 + a⁻¹)`). -/
lemma two_mul_div_le_log {y : ℝ} (hy : 1 ≤ y) : 2 * (y - 1) / (y + 1) ≤ Real.log y := by
  rcases eq_or_lt_of_le hy with h | h
  · subst h; simp
  · have hy1 : 0 < y - 1 := by linarith
    have ha : 0 < 1 / (y - 1) := by positivity
    have hs := Real.hasSum_log_one_add_inv ha
    have h1 : 1 + (1 / (y - 1))⁻¹ = y := by field_simp; ring
    rw [h1] at hs
    have h2 := le_hasSum hs 0 (fun j _ => by positivity)
    have h3 : (2 : ℝ) * (1 / (2 * ((0 : ℕ) : ℝ) + 1)) * (1 / (2 * (1 / (y - 1)) + 1)) ^ (2 * 0 + 1)
        = 2 * (y - 1) / (y + 1) := by
      have hy2 : y + 1 ≠ 0 := by linarith
      have hy3 : y - 1 ≠ 0 := hy1.ne'
      have h4 : 2 * (1 / (y - 1)) + 1 = (y + 1) / (y - 1) := by
        field_simp; ring
      rw [h4]
      norm_num
      field_simp
    rw [h3] at h2
    exact h2

/-! ### One-step bounds for `log (k + 1) - log k` -/

lemma log_succ_sub_le (k : ℝ) (hk : 0 < k) : Real.log (k + 1) - Real.log k ≤ 1 / k := by
  rw [← Real.log_div (by linarith) hk.ne']
  have h := Real.log_le_sub_one_of_pos (show 0 < (k + 1) / k by positivity)
  have e : (k + 1) / k - 1 = 1 / k := by field_simp; ring
  linarith

lemma inv_succ_le_log_sub (k : ℝ) (hk : 0 < k) :
    1 / (k + 1) ≤ Real.log (k + 1) - Real.log k := by
  have h := Real.log_le_sub_one_of_pos (show 0 < k / (k + 1) by positivity)
  rw [Real.log_div hk.ne' (by linarith)] at h
  have e : k / (k + 1) - 1 = -(1 / (k + 1)) := by field_simp; ring
  linarith

lemma log_succ_sub_le_trap (k : ℝ) (hk : 0 < k) :
    Real.log (k + 1) - Real.log k ≤ (1 / k + 1 / (k + 1)) / 2 := by
  rw [← Real.log_div (by linarith) hk.ne']
  have h1 : 1 ≤ (k + 1) / k := by rw [le_div_iff₀ hk]; linarith
  have h := log_le_half_sub_inv h1
  have e : ((k + 1) / k - ((k + 1) / k)⁻¹) / 2 = (1 / k + 1 / (k + 1)) / 2 := by
    field_simp; ring
  linarith

/-! ### Harmonic sums `∑_{j=a}^{n-1} 1/j` -/

lemma harm_lower {a n : ℕ} (ha : 1 ≤ a) (han : a ≤ n) :
    Real.log n - Real.log a ≤ ∑ j ∈ Ico a n, (1 : ℝ) / j := by
  induction n, han using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [Finset.sum_Ico_succ_top hm]
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have h := log_succ_sub_le (m : ℝ) hm0
    push_cast
    linarith

lemma harm_upper {a n : ℕ} (ha : 1 ≤ a) (han : a ≤ n) :
    ∑ j ∈ Ico a n, (1 : ℝ) / j + 1 / n ≤ 1 / a + (Real.log n - Real.log a) := by
  induction n, han using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [Finset.sum_Ico_succ_top hm]
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have h := inv_succ_le_log_sub (m : ℝ) hm0
    push_cast
    linarith

lemma harm_trap {a n : ℕ} (ha : 1 ≤ a) (han : a ≤ n) :
    Real.log n - Real.log a + (1 / a - 1 / n) / 2 ≤ ∑ j ∈ Ico a n, (1 : ℝ) / j := by
  induction n, han using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [Finset.sum_Ico_succ_top hm]
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have h := log_succ_sub_le_trap (m : ℝ) hm0
    push_cast
    linarith

lemma sum_Icc_reindex (a n : ℕ) :
    ∑ i ∈ Icc (a + 1) n, 1 / ((i : ℝ) - 1) = ∑ j ∈ Ico a n, (1 : ℝ) / j := by
  rw [← Finset.Ico_add_one_right_eq_Icc, ← Finset.sum_Ico_add' (fun i : ℕ => 1 / ((i : ℝ) - 1)) a n 1]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  push_cast
  ring_nf

/-! ### Two-sided bound on the success probability of a cutoff rule -/

open ClassicalSecretary in
lemma successProb_cutoff_bounds (n r : ℕ) (hr : 1 ≤ r) (hrn : r ≤ n) :
    -(((r : ℝ) - 1) / n) * Real.log (((r : ℝ) - 1) / n) ≤ successProb n (cutoffRule r) ∧
    successProb n (cutoffRule r) ≤
      -(((r : ℝ) - 1) / n) * Real.log (((r : ℝ) - 1) / n) + 1 / n := by
  have hn : 1 ≤ n := le_trans hr hrn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rcases eq_or_lt_of_le hr with h | h
  · subst h
    rw [successProb_cutoffRule_one n hn]
    simp
  · obtain ⟨a, rfl⟩ : ∃ a, r = a + 1 := ⟨r - 1, by omega⟩
    have ha : 1 ≤ a := by omega
    have han : a ≤ n := by omega
    rw [successProb_cutoffRule n (a + 1) h hrn, sum_Icc_reindex]
    push_cast
    simp only [add_sub_cancel_right]
    have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
    rw [Real.log_div ha0.ne' hn0.ne']
    have hL := harm_lower ha han
    have hU := harm_upper ha han
    have hx : 0 ≤ (a : ℝ) / n := by positivity
    constructor
    · have := mul_le_mul_of_nonneg_left hL hx
      linarith
    · have h1 := mul_le_mul_of_nonneg_left hU hx
      have e1 : (a : ℝ) / n * (1 / a + (Real.log n - Real.log a)) =
          1 / n + (a / n) * (Real.log n - Real.log a) := by
        field_simp
      have e2 : 0 ≤ (a : ℝ) / n * (1 / n) := by positivity
      nlinarith

open ClassicalSecretary in
/-- Trapezoid refinement of the lower bound. -/
lemma successProb_cutoff_trap (n a : ℕ) (ha : 1 ≤ a) (han : a < n) :
    -((a : ℝ) / n) * Real.log ((a : ℝ) / n) + (1 - (a : ℝ) / n) / (2 * n) ≤
      successProb n (cutoffRule (a + 1)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [successProb_cutoffRule n (a + 1) (by omega) (by omega), sum_Icc_reindex]
  push_cast
  simp only [add_sub_cancel_right]
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  rw [Real.log_div ha0.ne' hn0.ne']
  have hT := harm_trap ha han.le
  have hx : 0 ≤ (a : ℝ) / n := by positivity
  have h1 := mul_le_mul_of_nonneg_left hT hx
  have e1 : (a : ℝ) / n * (Real.log n - Real.log a + (1 / a - 1 / n) / 2) =
      -((a : ℝ) / n) * (Real.log a - Real.log n) + (1 - (a : ℝ) / n) / (2 * n) := by
    field_simp
    ring
  linarith

/-! ### Quadratic bounds for `g x = -x log x` around its maximum `e⁻¹` -/

lemma exp_neg_one_mul_exp_one : Real.exp (-1) * Real.exp 1 = 1 := by
  rw [← Real.exp_add]; simp

lemma exp_neg_one_lt_one : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)

lemma log_exp_neg_one_mul {y : ℝ} (hy : 0 < y) :
    Real.log (Real.exp (-1) * y) = Real.log y - 1 := by
  rw [Real.log_mul (Real.exp_pos _).ne' hy.ne', Real.log_exp]; ring

/-- Lower quadratic bound for `x ≥ e⁻¹` (since `g'' = -1/x ≥ -e`). -/
lemma quad_le_negMulLog (x : ℝ) (hx : Real.exp (-1) ≤ x) :
    Real.exp (-1) - Real.exp 1 / 2 * (x - Real.exp (-1)) ^ 2 ≤ -x * Real.log x := by
  have hcE := exp_neg_one_mul_exp_one
  set c := Real.exp (-1) with hc
  set E := Real.exp 1 with hE
  have hc0 : 0 < c := Real.exp_pos _
  have hE0 : 0 < E := Real.exp_pos _
  obtain ⟨y, hy, rfl⟩ : ∃ y, 1 ≤ y ∧ x = c * y := by
    refine ⟨E * x, ?_, ?_⟩
    · have := mul_le_mul_of_nonneg_left hx hE0.le
      linarith
    · rw [← mul_assoc, hcE, one_mul]
  have hy0 : 0 < y := by linarith
  rw [log_exp_neg_one_mul hy0]
  have h1 := log_le_half_sub_inv hy
  have P := mul_le_mul_of_nonneg_left h1 (mul_pos hc0 hy0).le
  have h4 : c * y * y⁻¹ = c := by field_simp
  have key : c - E / 2 * (c * y - c) ^ 2 = c / 2 + c * y - c * y ^ 2 / 2 := by
    linear_combination (-(c / 2) * (y - 1) ^ 2) * hcE
  rw [key]
  nlinarith

/-- Strong concavity: `g x ≤ e⁻¹ - (x - e⁻¹)²/2` on `[0, 1]`. -/
lemma negMulLog_le_quad (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    -x * Real.log x ≤ Real.exp (-1) - (x - Real.exp (-1)) ^ 2 / 2 := by
  have hcE := exp_neg_one_mul_exp_one
  have hc1 := exp_neg_one_lt_one
  set c := Real.exp (-1) with hc
  set E := Real.exp 1 with hE
  have hc0 : 0 < c := Real.exp_pos _
  have hE0 : 0 < E := Real.exp_pos _
  rcases eq_or_lt_of_le hx0 with h0 | h0
  · subst h0
    simp only [neg_zero, zero_mul, zero_sub, even_two, Even.neg_pow]
    nlinarith
  obtain ⟨y, hy0, rfl⟩ : ∃ y, 0 < y ∧ x = c * y := by
    refine ⟨E * x, by positivity, ?_⟩
    rw [← mul_assoc, hcE, one_mul]
  rw [log_exp_neg_one_mul hy0]
  rcases le_total y 1 with hy1 | hy1
  · have h1 := half_sub_inv_le_log hy0 hy1
    have P := mul_le_mul_of_nonneg_left h1 (mul_pos hc0 hy0).le
    have h4 : c * y * y⁻¹ = c := by field_simp
    have Q : 0 ≤ c * (y - 1) ^ 2 * (1 - c) := by
      apply mul_nonneg (mul_nonneg hc0.le (sq_nonneg _)); linarith
    nlinarith
  · have h1 := two_mul_div_le_log hy1
    have hy2 : 0 < y + 1 := by linarith
    rw [div_le_iff₀ hy2] at h1
    have P := mul_le_mul_of_nonneg_left h1 (mul_pos hc0 hy0).le
    have Q : 0 ≤ c * (y - 1) ^ 2 * (2 - c * (y + 1)) := by
      apply mul_nonneg (mul_nonneg hc0.le (sq_nonneg _)); nlinarith
    refine le_of_mul_le_mul_right ?_ hy2
    nlinarith

/-- `g x ≤ e⁻¹` on `[0, 1]`. -/
lemma negMulLog_le (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    -x * Real.log x ≤ Real.exp (-1) := by
  have := negMulLog_le_quad x hx0 hx1
  nlinarith [sq_nonneg (x - Real.exp (-1))]

end ClassicalSecretary.SecAn

open ClassicalSecretary in
theorem solution :
    Tendsto optimalProb atTop (𝓝 (Real.exp (-1))) := by
  have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hup : Tendsto (fun n : ℕ => Real.exp (-1) + 1 / n) atTop (𝓝 (Real.exp (-1))) := by
    have := h1.const_add (Real.exp (-1))
    rwa [add_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn using exp_neg_one_le_optimalProb n hn
  · filter_upwards [eventually_ge_atTop 1] with n hn
    obtain ⟨r, h1r, hrn, hP⟩ := exists_optimal_cutoffRule n hn
    rw [← hP]
    have hb := (ClassicalSecretary.SecAn.successProb_cutoff_bounds n r h1r hrn).2
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast h1r
    have hrn' : (r : ℝ) ≤ n := by exact_mod_cast hrn
    have hx0 : 0 ≤ ((r : ℝ) - 1) / n := div_nonneg (by linarith) hn0.le
    have hx1 : ((r : ℝ) - 1) / n ≤ 1 := by
      rw [div_le_one hn0]; linarith
    have hg := ClassicalSecretary.SecAn.negMulLog_le _ hx0 hx1
    linarith
