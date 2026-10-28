-- Prove2me | solution 1 for AvramDividend.Classical.nonnegative_scalar_real_density_Ioc_intervalIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T11:41:15.191159+00:00
-- url     : https://prove2.me/submissions/205c0b0b-4c0d-41ed-816a-2c7ca87ad00d

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_AvramDividend_Classical_nonnegative_real_density_Ioc_toReal_eq_intervalIntegral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

/-- A nonnegative real scalar multiplies the primitive of a real density. -/
theorem solution (r : ℝ) (hr : 0 ≤ r)
    (f : ℝ → ℝ) (hfpos : ∀ y : ℝ, 0 ≤ f y)
    (x : ℝ) (hx : 0 ≤ x) (hfi : IntervalIntegrable f volume 0 x) :
    ((ENNReal.ofReal r • volume.withDensity
      (fun y : ℝ => ENNReal.ofReal (f y))) (Ioc (0 : ℝ) x)).toReal =
      r * ∫ y in (0 : ℝ)..x, f y := by
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hr]
  rw [nonnegative_real_density_Ioc_toReal_eq_intervalIntegral f hfpos x hx hfi]
