-- Prove2me | solution 2 for AvramDividend.Classical.nonnegative_scalar_real_density_Ioc_intervalIntegral
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T11:41:30.710264+00:00
-- url     : https://prove2.me/submissions/d8d24c2f-60cf-4f02-983b-d70f6bf17253

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_AvramDividend_Classical_nonnegative_real_density_Ioc_toReal_eq_intervalIntegral
open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal
theorem solution (r : ℝ) (hr : 0 ≤ r)
    (f : ℝ → ℝ) (hfpos : ∀ y : ℝ, 0 ≤ f y)
    (x : ℝ) (hx : 0 ≤ x) (hfi : IntervalIntegrable f volume 0 x) :
    ((ENNReal.ofReal r • volume.withDensity
      (fun y : ℝ => ENNReal.ofReal (f y))) (Ioc (0 : ℝ) x)).toReal =
      r * ∫ y in (0 : ℝ)..x, f y := by
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hr,
    AvramDividend.Classical.nonnegative_real_density_Ioc_toReal_eq_intervalIntegral f hfpos x hx hfi]
