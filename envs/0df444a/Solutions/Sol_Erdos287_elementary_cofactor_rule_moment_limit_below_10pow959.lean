-- Prove2me | solution 1 for Erdos287.elementary_cofactor_rule_moment_limit_below_10pow959
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T12:34:59.21547+00:00
-- url     : https://prove2.me/submissions/2746109f-e484-4ed8-bd00-60b79304d029

import Mathlib
import Theorems.Thm_Erdos287_grouped_moments_require_cofactor_budget

set_option autoImplicit false
set_option maxRecDepth 12000
set_option exponentiation.threshold 4096

/-- Below the stated finite range, the elementary least-common-multiple
omission rule cannot supply the cofactor budget for this moment test. -/
theorem solution (B p M : ℕ) (N T σ r A μ : ℝ)
    (hsmall : B * Nat.lcmUpto B < p) (hpM : p ≤ M) (hM : M ≤ 10 ^ (959 : ℕ))
    (hN : 11 ≤ N) (hT : 0 ≤ T ∧ T ≤ 2 * (B : ℝ) * N)
    (hσ : 0 ≤ σ ∧ σ ≤ 1 / 4) (hA : 18 / 5 ≤ A) (hAr : A < r)
    (hr : r ≤ 93 / 25) (hmean : N * μ ≤ 2 * σ * Real.log (1 + T)) :
    μ * (r - A) ≤ 1 - A * σ := by
  have hB : B ≤ 3186 := by
    by_contra! hlarge
    have hB₁ : B + 1 ≤ 2 * B := by omega
    have hbound : 2 ^ B < 2 * 10 ^ (959 : ℕ) := calc
      2 ^ B ≤ (B + 1) * Nat.lcmUpto B := Chebyshev.two_pow_le_mul_lcmUpto B
      _ ≤ 2 * (B * Nat.lcmUpto B) := by
        simpa only [mul_assoc] using Nat.mul_le_mul_right (Nat.lcmUpto B) hB₁
      _ < 2 * p := Nat.mul_lt_mul_of_pos_left hsmall (by decide)
      _ ≤ _ := Nat.mul_le_mul_left _ (hpM.trans hM)
    have hpow : (2 : ℕ) ^ 3187 ≤ 2 ^ B := Nat.pow_le_pow_right (by decide) (by omega)
    have hnumeric : (2 : ℕ) * 10 ^ (959 : ℕ) < 2 ^ (3187 : ℕ) := by norm_num
    exact (hnumeric.trans_le hpow).not_ge hbound.le
  by_contra! hstrict
  have hrequired := Erdos287.grouped_moments_require_cofactor_budget N B T σ r A μ
    hN (Nat.cast_nonneg B) hT hσ hA hAr hr hmean hstrict
  have hmax : (B : ℝ) ≤ 3186 := by exact_mod_cast hB
  have hexp : (2 : ℝ) ^ 17 < Real.exp 17 := by
    rw [show (17 : ℝ) = (17 : ℕ) * (1 : ℝ) by norm_num, Real.exp_nat_mul]
    exact pow_lt_pow_left₀ (by linarith [Real.exp_one_gt_d9]) (by norm_num) (by decide)
  have harg : 1 + 22 * (B : ℝ) < Real.exp (55 / 3) := calc
    1 + 22 * (B : ℝ) < (2 : ℝ) ^ 17 := by norm_num; linarith only [hmax]
    _ < Real.exp 17 := hexp
    _ < _ := Real.exp_lt_exp.mpr (by norm_num)
  have hlog : Real.log (1 + 22 * (B : ℝ)) < 55 / 3 :=
    (Real.log_lt_iff_lt_exp (by positivity)).mpr harg
  exact hrequired.not_ge hlog.le

