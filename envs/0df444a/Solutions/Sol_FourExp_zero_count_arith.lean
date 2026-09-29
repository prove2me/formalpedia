-- Prove2me | solution 1 for FourExp.zero_count_arith
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-15T08:40:12.011328+00:00
-- url     : https://prove2.me/submissions/5f5f312e-07b8-4f35-a6a9-d287952ca0ff

import Mathlib

namespace FourExpArith

/-- `n!·2ⁿ ≤ 2·nⁿ` for `n ≥ 2`, from `(1 + 1/n)ⁿ ≥ 2`. -/
lemma fact_two_pow_le (n : ℕ) (hn : 2 ≤ n) :
    (n.factorial : ℝ) * 2 ^ n ≤ 2 * (n : ℝ) ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [Nat.factorial]
  | succ m hm ih =>
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have key : 2 * (m : ℝ) ^ m ≤ ((m : ℝ) + 1) ^ m := by
      have h1 := one_add_mul_le_pow (a := 1 / (m : ℝ))
        (by have : (0 : ℝ) ≤ 1 / m := by positivity
            linarith) m
      rw [mul_one_div_cancel hm0.ne'] at h1
      have h3 : ((m : ℝ) + 1) ^ m = (1 + 1 / (m : ℝ)) ^ m * (m : ℝ) ^ m := by
        rw [← mul_pow, add_mul, one_mul, div_mul_cancel₀ _ hm0.ne']
      rw [h3]
      calc 2 * (m : ℝ) ^ m = (1 + 1) * (m : ℝ) ^ m := by ring
        _ ≤ (1 + 1 / (m : ℝ)) ^ m * (m : ℝ) ^ m :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
    rw [Nat.factorial_succ]
    push_cast
    calc ((m : ℝ) + 1) * m.factorial * 2 ^ (m + 1)
        = 2 * ((m : ℝ) + 1) * (m.factorial * 2 ^ m) := by ring
      _ ≤ 2 * ((m : ℝ) + 1) * (2 * (m : ℝ) ^ m) :=
          mul_le_mul_of_nonneg_left ih (by positivity)
      _ ≤ 2 * ((m : ℝ) + 1) * ((m : ℝ) + 1) ^ m :=
          mul_le_mul_of_nonneg_left key (by positivity)
      _ = 2 * ((m : ℝ) + 1) ^ (m + 1) := by ring

lemma exp_two_gt_six : (6 : ℝ) < Real.exp 2 := by
  have h := Real.exp_one_gt_d9
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [h2]
  nlinarith

lemma log_three_lt : Real.log 3 < 4 / 3 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.add_one_le_exp (1 / 3 : ℝ)
  have h3 : Real.exp (4 / 3) = Real.exp 1 * Real.exp (1 / 3) := by
    rw [← Real.exp_add]; norm_num
  rw [h3]
  nlinarith [mul_le_mul h1.le h2 (by norm_num) (Real.exp_pos 1).le]

/-- The core inequality: with `R = x + (x+1)u` and `u ≥ 3`, the right-hand side of the hypothesis
is below `n log n + 2(1+u)(1+x)`. -/
lemma core (n : ℕ) (hn : 2 ≤ n) (x : ℝ) (hx : 0 ≤ x) (u : ℝ) (hu : 3 ≤ u) :
    Real.log ((n.factorial : ℝ) * 2 ^ (n + 1) * (x + (x + 1) * u) / (x + (x + 1) * u - 1))
      + 2 * (x + (x + 1) * u) < n * Real.log n + 2 * (1 + u) * (1 + x) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  obtain ⟨R, hR⟩ : ∃ R, R = x + (x + 1) * u := ⟨_, rfl⟩
  rw [← hR]
  have hR3 : 3 ≤ R := by rw [hR]; nlinarith
  have hR1 : 0 < R - 1 := by linarith
  have hfrac : R / (R - 1) ≤ 3 / 2 := by rw [div_le_iff₀ hR1]; linarith
  have hfact : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hpos : 0 < (n.factorial : ℝ) * 2 ^ (n + 1) * R / (R - 1) :=
    div_pos (mul_pos (mul_pos hfact (by positivity)) (by linarith)) hR1
  have hnn : (0 : ℝ) < (n : ℝ) ^ n := by positivity
  have hbound : (n.factorial : ℝ) * 2 ^ (n + 1) * R / (R - 1)
      < Real.exp (n * Real.log n + 2) := by
    rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hn0]
    calc (n.factorial : ℝ) * 2 ^ (n + 1) * R / (R - 1)
        = 2 * ((n.factorial : ℝ) * 2 ^ n) * (R / (R - 1)) := by rw [pow_succ]; ring
      _ ≤ 2 * (2 * (n : ℝ) ^ n) * (3 / 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (fact_two_pow_le n hn) (by norm_num)) hfrac
            (div_pos (by linarith) hR1).le (by positivity)
      _ = 6 * (n : ℝ) ^ n := by ring
      _ < Real.exp 2 * (n : ℝ) ^ n := mul_lt_mul_of_pos_right exp_two_gt_six hnn
      _ = (n : ℝ) ^ n * Real.exp 2 := by ring
  have hlog := (Real.log_lt_iff_lt_exp hpos).2 hbound
  have h2R : 2 * R = 2 * (1 + u) * (1 + x) - 2 := by rw [hR]; ring
  linarith

end FourExpArith

theorem solution
    (n : ℕ) (hn : 2 ≤ n) (x lam : ℝ) (hx : 0 ≤ x) (hlam : 0 < lam) (σ : ℝ) (hσ : 0 ≤ σ)
    (h : ∀ R : ℝ, x + 1 < R →
      σ * Real.log ((R - x) / (x + 1)) ≤ Real.log ((n.factorial : ℝ) * 2 ^ (n + 1) * R / (R - 1)) + 2 * R) :
    σ < (n : ℝ) / lam + 2 * (1 + (n : ℝ) ^ lam) / (lam * Real.log (n : ℝ)) * (1 + x) := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hn0 : (0 : ℝ) < n := by linarith
  have hL : 0 < Real.log n := Real.log_pos hn1
  obtain ⟨t, ht⟩ : ∃ t, t = (n : ℝ) ^ lam := ⟨_, rfl⟩
  rw [← ht]
  have hlogt : Real.log t = lam * Real.log n := by rw [ht]; exact Real.log_rpow hn0 lam
  have hlt : 0 < Real.log t := by rw [hlogt]; exact mul_pos hlam hL
  have ht0 : 0 < t := by rw [ht]; exact Real.rpow_pos_of_pos hn0 lam
  -- Apply the hypothesis at `R = x + (x+1)u` with `u = max t 3`.
  obtain ⟨u, hu⟩ : ∃ u, u = max t 3 := ⟨_, rfl⟩
  have hu3 : 3 ≤ u := by rw [hu]; exact le_max_right _ _
  have hu1 : 1 < u := by linarith
  have hlogu : 0 < Real.log u := Real.log_pos hu1
  have hRgt : x + 1 < x + (x + 1) * u := by
    have := mul_lt_mul_of_pos_left hu1 (by linarith : (0 : ℝ) < x + 1)
    linarith
  have hH := h _ hRgt
  have hq : (x + (x + 1) * u - x) / (x + 1) = u := by
    rw [add_sub_cancel_left, mul_div_cancel_left₀ _ (by linarith : (x + 1 : ℝ) ≠ 0)]
  rw [hq] at hH
  have hσu : σ * Real.log u < n * Real.log n + 2 * (1 + u) * (1 + x) :=
    lt_of_le_of_lt hH (FourExpArith.core n hn x hx u hu3)
  -- Passing from `u` back to `t`.
  have hmono : (n * Real.log n + 2 * (1 + u) * (1 + x)) * Real.log t
      ≤ (n * Real.log n + 2 * (1 + t) * (1 + x)) * Real.log u := by
    rcases le_or_gt 3 t with h3 | h3
    · rw [hu, max_eq_left h3]
    · rw [hu, max_eq_right h3.le]
      have hlt3 : Real.log t ≤ Real.log 3 := Real.log_le_log ht0 h3.le
      have htan : Real.log (t / 3) ≤ t / 3 - 1 := Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_div ht0.ne' (by norm_num)] at htan
      have hl3 := FourExpArith.log_three_lt
      have hnL : 0 ≤ (n : ℝ) * Real.log n := mul_nonneg hn0.le hL.le
      have hx1 : 0 ≤ 1 + x := by linarith
      have h4 : 4 * Real.log t ≤ (1 + t) * Real.log 3 := by
        nlinarith [mul_pos (sub_pos.2 h3) (sub_pos.2 hl3)]
      nlinarith [mul_le_mul_of_nonneg_left hlt3 hnL, mul_le_mul_of_nonneg_left h4 hx1]
  have hσt : σ * Real.log t < n * Real.log n + 2 * (1 + t) * (1 + x) := by
    have h1 := mul_lt_mul_of_pos_right hσu hlt
    have h2 : σ * Real.log t * Real.log u
        < (n * Real.log n + 2 * (1 + t) * (1 + x)) * Real.log u := by linarith
    exact lt_of_mul_lt_mul_right h2 hlogu.le
  have hlam0 := hlam.ne'
  have hL0 := hL.ne'
  have hgoal : (n : ℝ) / lam + 2 * (1 + t) / (lam * Real.log n) * (1 + x)
      = (n * Real.log n + 2 * (1 + t) * (1 + x)) / Real.log t := by
    rw [hlogt]
    field_simp
  rw [hgoal, lt_div_iff₀ hlt]
  exact hσt
