-- Prove2me | solution 1 for AvramDividend.Classical.double_scalar_measure_convolution
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T11:24:24.147117+00:00
-- url     : https://prove2.me/submissions/c1cfe4d4-225e-4e24-b165-ac245659a8bb

import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Measure.WithDensity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal

/-- Pull both nonnegative scalar weights out of convolution of finite-type measures. -/
theorem solution
    (a b : ℝ≥0∞) (μ ν : Measure ℝ) [SFinite μ] [SFinite ν] :
    (a • μ).conv (b • ν) = (a * b) • (μ.conv ν) := by
  simp [Measure.conv_smul_left, Measure.conv_smul_right, smul_smul, mul_comm]
