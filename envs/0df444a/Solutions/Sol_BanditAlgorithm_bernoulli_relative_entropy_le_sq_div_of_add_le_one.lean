-- Prove2me | solution 1 for BanditAlgorithm.bernoulli_relative_entropy_le_sq_div_of_add_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-05T18:32:43.72153+00:00
-- url     : https://prove2.me/submissions/2b8bd5c5-2c36-4e87-a96f-ee3556340515

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_bernoulliRelativeEntropy
import Theorems.Thm_Real_two_mul_sub_one_div_add_one_le_log
import Theorems.Thm_Real_log_le_sub_inv_div_two

theorem solution
    {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hsum : p + q ≤ 1) :
    BanditAlgorithm.bernoulliRelativeEntropy p q ≤ (q - p) ^ 2 / (p * (2 - p - q)) := by
  have hq0 : 0 < q := lt_trans hp hpq
  have hq : q < 1 := by linarith
  have hp1 : p < 1 := lt_trans hpq hq
  have h1q : (0:ℝ) < 1 - q := by linarith
  have h1p : (0:ℝ) < 1 - p := by linarith
  have h2pq : (1:ℝ) ≤ 2 - p - q := by linarith
  -- first term, via the Pade lower bound for `log` on `[1, ∞)`
  have ht1 : (1:ℝ) ≤ q / p := (one_le_div hp).mpr hpq.le
  have hlog1 : Real.log (p / q) ≤ -(2 * (q - p) / (q + p)) := by
    have h := Real.two_mul_sub_one_div_add_one_le_log ht1
    have hrw : p / q = (q / p)⁻¹ := (inv_div q p).symm
    rw [hrw, Real.log_inv]
    have hd1 : (0:ℝ) < q / p + 1 := add_pos (div_pos hq0 hp) one_pos
    have hd2 : (0:ℝ) < q + p := by linarith
    have heq : 2 * (q / p - 1) / (q / p + 1) = 2 * (q - p) / (q + p) := by
      rw [div_eq_div_iff (ne_of_gt hd1) (ne_of_gt hd2)]
      field_simp
    rw [heq] at h
    linarith
  -- second term, via the sinh upper bound for `log` on `[1, ∞)`
  have ht2 : (1:ℝ) ≤ (1 - p) / (1 - q) := (one_le_div h1q).mpr (by linarith)
  have hlog2 : Real.log ((1 - p) / (1 - q))
      ≤ ((1 - p) / (1 - q) - (1 - q) / (1 - p)) / 2 := by
    have h := Real.log_le_sub_inv_div_two ht2
    rw [one_div, inv_div] at h
    exact h
  have hres : (q - p) ^ 2 / (p * (2 - p - q))
      - (p * (-(2 * (q - p) / (q + p)))
          + (1 - p) * (((1 - p) / (1 - q) - (1 - q) / (1 - p)) / 2))
      = (q - p) ^ 3 * (2 - 2 * q - p * q - p ^ 2)
          / (2 * p * (p + q) * (1 - q) * (2 - p - q)) := by
    field_simp
    ring
  have hpos : 0 ≤ (q - p) ^ 3 * (2 - 2 * q - p * q - p ^ 2)
      / (2 * p * (p + q) * (1 - q) * (2 - p - q)) := by
    apply div_nonneg
    · have hA : (0:ℝ) < (q - p) ^ 3 := pow_pos (by linarith) 3
      have hB : (0:ℝ) ≤ 2 - 2 * q - p * q - p ^ 2 := by nlinarith
      exact mul_nonneg hA.le hB
    · have h2p : (0:ℝ) < 2 * p := by linarith
      have hpq' : (0:ℝ) < p + q := by linarith
      exact le_of_lt (mul_pos (mul_pos (mul_pos h2p hpq') h1q) (by linarith))
  have hbound : p * Real.log (p / q) ≤ p * (-(2 * (q - p) / (q + p))) :=
    mul_le_mul_of_nonneg_left hlog1 hp.le
  have hbound2 : (1 - p) * Real.log ((1 - p) / (1 - q))
      ≤ (1 - p) * (((1 - p) / (1 - q) - (1 - q) / (1 - p)) / 2) :=
    mul_le_mul_of_nonneg_left hlog2 h1p.le
  rw [BanditAlgorithm.bernoulliRelativeEntropy]
  linarith
