-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_positive_uniform_mesh_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:59:53.496775+00:00
-- url     : https://prove2.me/submissions/dea9db6a-9265-4b39-9432-36e0d01e1487

import Mathlib
-- Exact pinned Mathlib imports are retained for Real, NNReal and Tendsto.

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- The original positive uniform mesh T/(n+1) tends to zero from above. -/
theorem solution
    (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n : ℕ => (T : ℝ) / ((n : ℝ) + 1))
      atTop (nhdsWithin (0 : ℝ) (Ioi 0)) := by
  have hBase :
      Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hMul := hBase.const_mul (T : ℝ)
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa only [mul_zero, one_div, div_eq_mul_inv, one_mul] using hMul
  · exact Filter.Eventually.of_forall (by
      intro n
      have hTR : 0 < (T : ℝ) := by exact_mod_cast hT
      exact div_pos hTR (by positivity))
