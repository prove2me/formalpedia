-- Prove2me | solution 1 for ForecastAggLearn.logLoss_proper
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-06T12:12:31.123638+00:00
-- url     : https://prove2.me/submissions/660c20b7-3ec1-4c78-b423-254a10b7ebc6

import Definitions.Def_ForecastAggLearn_logLoss
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open ForecastAggLearn

private lemma weighted_log_bound (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a * (Real.log b - Real.log a) ≤ b - a := by
  have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hb ha)) ha.le
  rw [Real.log_div hb.ne' ha.ne'] at h
  have heq : a * (b / a - 1) = b - a := by field_simp
  rwa [heq] at h

theorem solution (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ENNReal.ofReal q * logLoss q true + ENNReal.ofReal (1 - q) * logLoss q false ≤
      ENNReal.ofReal q * logLoss r true + ENNReal.ofReal (1 - q) * logLoss r false := by
  by_cases hqz : q = 0
  · subst q
    norm_num [logLoss]
  by_cases hqo : q = 1
  · subst q
    norm_num [logLoss]
  have hq : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hqz)
  have hq' : q < 1 := lt_of_le_of_ne hq1 hqo
  have hqc : 0 < 1 - q := sub_pos.mpr hq'
  by_cases hrz : r = 0
  · subst r
    simp [logLoss, ENNReal.ofReal_ne_zero_iff.mpr hq]
  by_cases hro : r = 1
  · subst r
    simp [logLoss, ENNReal.ofReal_ne_zero_iff.mpr hqc]
  have hr : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hrz)
  have hr' : r < 1 := lt_of_le_of_ne hr1 hro
  have hrc : 0 < 1 - r := sub_pos.mpr hr'
  have hlogq : 0 ≤ -Real.log q := neg_nonneg.mpr (Real.log_nonpos hq0 hq1)
  have hlogqc : 0 ≤ -Real.log (1 - q) :=
    neg_nonneg.mpr (Real.log_nonpos hqc.le (by linarith))
  have hlogr : 0 ≤ -Real.log r := neg_nonneg.mpr (Real.log_nonpos hr0 hr1)
  have hlogrc : 0 ≤ -Real.log (1 - r) :=
    neg_nonneg.mpr (Real.log_nonpos hrc.le (by linarith))
  simp [logLoss, not_le.mpr hq, not_le.mpr hq', not_le.mpr hr, not_le.mpr hr']
  rw [← ENNReal.ofReal_mul hq0, ← ENNReal.ofReal_mul hqc.le,
    ← ENNReal.ofReal_mul hq0, ← ENNReal.ofReal_mul hqc.le,
    ← ENNReal.ofReal_add (mul_nonneg hq0 hlogq) (mul_nonneg hqc.le hlogqc),
    ← ENNReal.ofReal_add (mul_nonneg hq0 hlogr) (mul_nonneg hqc.le hlogrc)]
  apply ENNReal.ofReal_le_ofReal
  have h1 := weighted_log_bound q r hq hr
  have h2 := weighted_log_bound (1 - q) (1 - r) hqc hrc
  nlinarith
#print axioms solution
