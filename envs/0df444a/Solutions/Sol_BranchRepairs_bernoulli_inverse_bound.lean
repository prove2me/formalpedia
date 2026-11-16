-- Prove2me | solution 1 for BranchRepairs.bernoulli_inverse_bound
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-16T03:28:10.149206+00:00
-- url     : https://prove2.me/submissions/675fed00-73ae-447a-aeaa-f9f2b849aa6a

import Mathlib
open Filter Topology

theorem solution (m : ℕ) (d z : ℝ)
    (hd : 0 ≤ d) (hz : 0 < z) :
    ((1 + d/z)^m)⁻¹ ≤ (1 + (m:ℝ)*d/z)⁻¹ := by
  have ht : 0 ≤ d/z := div_nonneg hd hz.le
  have hb := one_add_mul_le_pow (R := ℝ) (by linarith : -2 ≤ d/z) m
  have hp : 0 < 1 + (m:ℝ)*(d/z) := by positivity
  have hi := one_div_le_one_div_of_le hp hb
  simpa only [one_div, mul_div_assoc] using hi
