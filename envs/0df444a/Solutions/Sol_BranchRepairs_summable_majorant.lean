-- Prove2me | solution 1 for BranchRepairs.summable_majorant
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-16T03:29:20.445195+00:00
-- url     : https://prove2.me/submissions/97aca1b9-91e5-4859-aeb1-7219d47c04ab

import Mathlib
open Filter Topology

theorem solution (m : ℕ) (d z : ℝ)
    (hm : 0 < m) (hd : 0 ≤ d) (hz : 0 < z) (hzm : z ≤ 2*(m:ℝ)) :
    ((1 + d/z)^m)⁻¹ ≤ (1 + d/2)⁻¹ := by
  have bernoulli_inverse_bound (m : ℕ) (d z : ℝ)
      (hd : 0 ≤ d) (hz : 0 < z) :
      ((1 + d/z)^m)⁻¹ ≤ (1 + (m:ℝ)*d/z)⁻¹ := by
    have ht : 0 ≤ d/z := div_nonneg hd hz.le
    have hb := one_add_mul_le_pow (R := ℝ) (by linarith : -2 ≤ d/z) m
    have hp : 0 < 1 + (m:ℝ)*(d/z) := by positivity
    have hi := one_div_le_one_div_of_le hp hb
    simpa only [one_div, mul_div_assoc] using hi
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hl : d/2 ≤ (m:ℝ)*d/z := by
    apply (le_div_iff₀ hz).mpr
    nlinarith [mul_le_mul_of_nonneg_left hzm hd]
  have hi : (1 + (m:ℝ)*d/z)⁻¹ ≤ (1+d/2)⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le (by positivity : 0 < 1+d/2)
        (show 1+d/2 ≤ 1+(m:ℝ)*d/z by linarith)
  exact (bernoulli_inverse_bound m d z hd hz).trans hi
