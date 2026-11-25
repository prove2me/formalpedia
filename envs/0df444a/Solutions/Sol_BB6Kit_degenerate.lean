-- Prove2me | solution 1 for BB6Kit.degenerate
-- status  : ACCEPTED   (prove)
-- author  : @alon yuval
-- created : 2026-11-23T22:14:08.029505+00:00
-- url     : https://prove2.me/submissions/6e5c24fa-a0ef-46be-b4f0-1cd0fb361494

import Mathlib
import Definitions.Def_BB6Delta
import Definitions.Def_BB6Kit
import Theorems.Thm_BB6Kit_laurent_23

namespace BB6KitDeg
theorem four_lt_three_pow (i : ℕ) (h : 5 ≤ i) : 4 * i + 8 ≤ 3 ^ i := by
  induction i, h using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ]; omega
theorem lt_two_pow (a : ℕ) : a < 2 ^ a := Nat.lt_two_pow_self
end BB6KitDeg

theorem solution (i k c : ℕ) (hi : 2 ^ 60 ≤ i) (hc : 0 < c) (hc4 : c ≤ 4 * i)
    (hk2 : 2 ≤ k) (hk : k ≤ 2 * i + 2)
    (hne : ((k : ℝ) - 1) * Real.log 2 - (i : ℝ) * Real.log 3 + Real.log (c : ℝ) ≠ 0) (hsm : ∃ a b : ℕ, c = 2 ^ a * 3 ^ b) :
    -(2 ^ 30 * Real.log (4 * (i : ℝ)) ^ 3) ≤ Real.log |((k : ℝ) - 1) * Real.log 2 - (i : ℝ) * Real.log 3 + Real.log (c : ℝ)| := by
  obtain ⟨a, b, rfl⟩ := hsm
  have hi5 : 5 ≤ i := le_trans (by norm_num) hi
  have hi0 : (0:ℝ) < i := by exact_mod_cast lt_of_lt_of_le (by norm_num) hi
  -- b < i and a < 4 i
  have h3b : 3 ^ b ≤ 4 * i := le_trans (Nat.le_mul_of_pos_left _ (by positivity)) hc4
  have h2a : 2 ^ a ≤ 4 * i := le_trans (Nat.le_mul_of_pos_right _ (by positivity)) hc4
  have hbi : b < i := by
    by_contra hb
    push_neg at hb
    have h1 : 3 ^ i ≤ 3 ^ b := Nat.pow_le_pow_right (by norm_num) hb
    have h2 := BB6KitDeg.four_lt_three_pow i hi5
    omega
  have hai : a < 4 * i := lt_of_lt_of_le (BB6KitDeg.lt_two_pow a) h2a
  -- rewrite Λ as a two-log form
  have hlog3 : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9
    linarith
  have hlog3' : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3)
    linarith
  have hΛ : ((k : ℝ) - 1) * Real.log 2 - (i : ℝ) * Real.log 3 + Real.log ((2 ^ a * 3 ^ b : ℕ) : ℝ) =
      -(((i - b : ℕ) : ℝ) * Real.log 3 - ((k - 1 + a : ℕ) : ℝ) * Real.log 2) := by
    rw [Nat.cast_sub hbi.le, Nat.cast_add, Nat.cast_sub (by omega : 1 ≤ k)]
    push_cast
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    ring
  rw [hΛ, abs_neg]
  have hL := BB6Kit.laurent_23 (k - 1 + a) (i - b) (by omega) (by omega)
  -- bound the max term
  set X : ℝ := ((k - 1 + a : ℕ) : ℝ) / Real.log 3 + ((i - b : ℕ) : ℝ) with hX
  have hX0 : 0 < X := by
    have : (0:ℝ) < ((i - b : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < i - b)
    have : (0:ℝ) ≤ ((k - 1 + a : ℕ) : ℝ) / Real.log 3 := by positivity
    linarith
  have hXle : X ≤ 8 * (i : ℝ) := by
    have e1 : ((k - 1 + a : ℕ) : ℝ) ≤ 6 * (i : ℝ) + 1 := by
      have : k - 1 + a ≤ 6 * i + 1 := by omega
      exact_mod_cast this
    have e2 : ((i - b : ℕ) : ℝ) ≤ (i : ℝ) := by exact_mod_cast Nat.sub_le i b
    have e3 : ((k - 1 + a : ℕ) : ℝ) / Real.log 3 ≤ ((k - 1 + a : ℕ) : ℝ) := by
      apply div_le_self (by positivity) hlog3.le
    have : (1:ℝ) ≤ i := by exact_mod_cast le_trans (by norm_num) hi
    linarith
  have h4i : (2:ℝ) ^ 62 ≤ 4 * (i : ℝ) := by
    have : (2:ℝ) ^ 60 ≤ (i : ℝ) := by exact_mod_cast hi
    have e : (2:ℝ) ^ 62 = 4 * 2 ^ 60 := by norm_num
    linarith
  have hlog4i : 42 ≤ Real.log (4 * (i : ℝ)) := by
    have h1 : Real.log ((2:ℝ) ^ 62) ≤ Real.log (4 * (i : ℝ)) := Real.log_le_log (by positivity) h4i
    rw [Real.log_pow] at h1
    have := Real.log_two_gt_d9
    push_cast at h1
    nlinarith
  have hlogX : Real.log X ≤ Real.log (4 * (i : ℝ)) + 1 := by
    have h1 : Real.log X ≤ Real.log (8 * (i : ℝ)) := Real.log_le_log hX0 hXle
    have h2 : Real.log (8 * (i : ℝ)) = Real.log 2 + Real.log (4 * (i : ℝ)) := by
      rw [show (8:ℝ) * i = 2 * (4 * i) by ring, Real.log_mul (by norm_num) (by positivity)]
    have := Real.log_two_lt_d9
    linarith
  have hmax : max (Real.log X + 0.38) 10 ≤ 2 * Real.log (4 * (i : ℝ)) := by
    apply max_le <;> linarith
  have hmax0 : 0 ≤ max (Real.log X + 0.38) 10 := le_trans (by norm_num) (le_max_right _ _)
  have hsq : (max (Real.log X + 0.38) 10) ^ 2 ≤ (2 * Real.log (4 * (i : ℝ))) ^ 2 :=
    pow_le_pow_left₀ hmax0 hmax 2
  have hl0 : 0 < Real.log (4 * (i : ℝ)) := by linarith
  have hfin : 25.2 * Real.log 3 * (max (Real.log X + 0.38) 10) ^ 2 ≤ 2 ^ 30 * Real.log (4 * (i : ℝ)) ^ 3 := by
    have a1 : 25.2 * Real.log 3 * (max (Real.log X + 0.38) 10) ^ 2 ≤ 25.2 * 2 * (2 * Real.log (4 * (i : ℝ))) ^ 2 := by
      have := mul_le_mul hlog3' hsq (by positivity) (by norm_num)
      nlinarith
    have a2 : 25.2 * 2 * (2 * Real.log (4 * (i : ℝ))) ^ 2 ≤ 2 ^ 30 * Real.log (4 * (i : ℝ)) ^ 3 := by
      have : Real.log (4 * (i : ℝ)) ^ 3 = Real.log (4 * (i : ℝ)) ^ 2 * Real.log (4 * (i : ℝ)) := by ring
      rw [this]
      have hsq0 : 0 ≤ Real.log (4 * (i : ℝ)) ^ 2 := sq_nonneg _
      nlinarith
    linarith
  linarith
