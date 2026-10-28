-- Prove2me | solution 1 for AvramDividend.Classical.geometric_atom_plus_real_density_positive_cumulative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T11:42:59.215911+00:00
-- url     : https://prove2.me/submissions/feb07654-5f71-4089-9358-a2eb99f66eee

import Mathlib.MeasureTheory.Measure.WithDensity
import Theorems.Thm_AvramDividend_Classical_nonnegative_scalar_real_density_Ioc_intervalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

/-- The positive-interval cumulative of an atom-plus-density renewal measure. -/
theorem solution
    (r : ℝ) (hr : 0 ≤ r) (f : ℝ → ℝ) (hfpos : ∀ y : ℝ, 0 ≤ f y)
    (β : Measure ℝ)
    (hβ : β = ENNReal.ofReal r • (Measure.dirac (0 : ℝ) +
      volume.withDensity (fun y : ℝ => ENNReal.ofReal (f y))))
    (x : ℝ) (hx : 0 ≤ x) (hfi : IntervalIntegrable f volume 0 x) :
    (β (Ioc (0 : ℝ) x)).toReal =
      r * ∫ y in (0 : ℝ)..x, f y := by
  calc
    (β (Ioc (0 : ℝ) x)).toReal =
        ((ENNReal.ofReal r • volume.withDensity
          (fun y : ℝ => ENNReal.ofReal (f y))) (Ioc (0 : ℝ) x)).toReal := by
      simp [hβ, Measure.smul_apply, Measure.add_apply]
    _ = r * ∫ y in (0 : ℝ)..x, f y :=
      nonnegative_scalar_real_density_Ioc_intervalIntegral
        r hr f hfpos x hx hfi
