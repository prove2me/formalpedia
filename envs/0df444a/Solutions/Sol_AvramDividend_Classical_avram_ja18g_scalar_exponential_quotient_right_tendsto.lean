-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18g_scalar_exponential_quotient_right_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T07:27:47.824854+00:00
-- url     : https://prove2.me/submissions/da36a172-e1be-4896-ba8d-9b0ba569e3c9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The right-hand slope of the scalar exponential, used in the original
    physical exponential-moment differentiation. -/
theorem solution (x : ℝ) :
    Filter.Tendsto (fun θ : ℝ => (Real.exp (θ * x) - 1) / θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds x) := by
  have hlin : HasDerivAt (fun θ : ℝ => θ * x) x 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const x
  have hexp : HasDerivAt (fun θ : ℝ => Real.exp (θ * x)) x 0 := by
    simpa only [Function.comp_def, zero_mul, Real.exp_zero, one_mul] using
      (Real.hasDerivAt_exp ((0 : ℝ) * x)).comp 0 hlin
  have hslope := hexp.tendsto_slope_zero_right
  simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using hslope
