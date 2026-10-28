-- Prove2me | solution 1 for AvramDividend.Classical.real_nonnegative_scalar_withDensity_unrestricted
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T22:20:51.600118+00:00
-- url     : https://prove2.me/submissions/a29f3521-48b6-4705-a73f-666904db930e

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real

open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution (r : ℝ) (hr : 0 ≤ r) (k : ℝ → ℝ) :
    ENNReal.ofReal r • (volume : Measure ℝ).withDensity
      (fun x : ℝ => ENNReal.ofReal (k x)) =
    (volume : Measure ℝ).withDensity
      (fun x : ℝ => ENNReal.ofReal (r * k x)) := by 
  rw [← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext x
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← ENNReal.ofReal_mul hr]
