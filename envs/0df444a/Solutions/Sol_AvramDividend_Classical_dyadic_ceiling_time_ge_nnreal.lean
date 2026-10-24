-- Prove2me | solution 1 for AvramDividend.Classical.dyadic_ceiling_time_ge_nnreal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:06:27.241773+00:00
-- url     : https://prove2.me/submissions/f48f5338-b656-4f29-8276-4e423f97e0f6

import Mathlib.Topology.Instances.NNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_rounding_bounds
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped NNReal

/-- Dyadic upward rounding dominates the original nonnegative-real time. -/
theorem solution
    (t : ℝ≥0) (n : ℕ) :
    t ≤ (Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) : ℝ≥0) / (2 : ℝ≥0) ^ n := by
  apply NNReal.coe_le_coe.mp
  simpa only [NNReal.coe_div, NNReal.coe_pow, NNReal.coe_natCast, NNReal.coe_ofNat]
    using (dyadic_ceiling_rounding_bounds t n).1
