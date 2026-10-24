-- Prove2me | solution 1 for AvramDividend.Classical.firstRecord_ofReal_geometric_tsum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:44:50.770595+00:00
-- url     : https://prove2.me/submissions/0d648e4f-70f2-4c67-b425-b0f1444cf30e

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal ENNReal BigOperators

/-! Sum discounted first-record real geometric weights in the extended nonnegative reals. -/
theorem solution
    (ε p : ℝ) (hε : 0 ≤ ε) (hp : 0 ≤ p) :
    (∑' n : ℕ, ENNReal.ofReal (ε * p ^ (n + 1))) =
      ENNReal.ofReal ε * (ENNReal.ofReal p * (1 - ENNReal.ofReal p)⁻¹) := by
  have hterm (n : ℕ) : ENNReal.ofReal (ε * p ^ (n + 1)) =
      ENNReal.ofReal ε * (ENNReal.ofReal p) ^ (n + 1) := by
    rw [ENNReal.ofReal_mul hε, ENNReal.ofReal_pow hp (n + 1)]
  simp_rw [hterm]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_add_one]
