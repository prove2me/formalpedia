-- Prove2me | solution 2 for AvramDividend.Classical.geometric_measure_sum_extract_constant
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T11:12:46.525163+00:00
-- url     : https://prove2.me/submissions/4848cc26-30ad-41f9-9726-948a2dbab851

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
open MeasureTheory
open scoped ENNReal NNReal
theorem solution
    (c : ℝ≥0∞) (m : ℕ → Measure ℝ) :
    Measure.sum (fun n : ℕ => c ^ (n + 1) • m n) =
      c • Measure.sum (fun n : ℕ => c ^ n • m n) := by
  ext s hs
  simp only [Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul, pow_succ', mul_assoc,
    ENNReal.tsum_mul_left]
