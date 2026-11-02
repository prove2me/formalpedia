-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_exp_quadratic_secant_right_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:18:13.574201+00:00
-- url     : https://prove2.me/submissions/86a9210d-6547-422a-b5ff-294d5e2cd033

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Quadratic-exponent Gaussian first-order exponential difference quotient. -/
theorem solution
    (b d : ℝ) :
    Filter.Tendsto
      (fun ε : ℝ => (Real.exp (b * ε + d * ε ^ 2) - 1) / ε)
      (𝓝[>] (0 : ℝ)) (𝓝 b) := by
  have hderiv :
      HasDerivAt (fun ε : ℝ => Real.exp (b * ε + d * ε ^ 2))
        b (0 : ℝ) := by
    convert (((hasDerivAt_id (0 : ℝ)).const_mul b).add
      (((hasDerivAt_id (0 : ℝ)).pow 2).const_mul d)).exp using 1 <;> simp
  have hlim := hderiv.tendsto_slope_zero_right
  convert hlim using 1
  funext ε
  simp [div_eq_mul_inv, mul_comm]
