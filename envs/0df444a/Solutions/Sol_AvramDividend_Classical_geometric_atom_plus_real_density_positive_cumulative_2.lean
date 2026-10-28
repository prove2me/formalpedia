-- Prove2me | solution 2 for AvramDividend.Classical.geometric_atom_plus_real_density_positive_cumulative
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T11:43:05.505823+00:00
-- url     : https://prove2.me/submissions/712dd5b9-b1ee-4a9a-a60a-489b0a76342f

import Mathlib.MeasureTheory.Measure.WithDensity
import Theorems.Thm_AvramDividend_Classical_nonnegative_scalar_real_density_Ioc_intervalIntegral
open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal
theorem solution
    (r : ℝ) (hr : 0 ≤ r) (f : ℝ → ℝ) (hfpos : ∀ y : ℝ, 0 ≤ f y)
    (β : Measure ℝ)
    (hβ : β = ENNReal.ofReal r • (Measure.dirac (0 : ℝ) +
      volume.withDensity (fun y : ℝ => ENNReal.ofReal (f y))))
    (x : ℝ) (hx : 0 ≤ x) (hfi : IntervalIntegrable f volume 0 x) :
    (β (Ioc (0 : ℝ) x)).toReal =
      r * ∫ y in (0 : ℝ)..x, f y := by
  rw [hβ, smul_add, Measure.add_apply, Measure.smul_apply (μ := Measure.dirac (0 : ℝ)),
    Measure.dirac_apply' _ measurableSet_Ioc, Set.indicator_of_notMem (by simp), smul_zero, zero_add]
  exact AvramDividend.Classical.nonnegative_scalar_real_density_Ioc_intervalIntegral r hr f hfpos x hx hfi
