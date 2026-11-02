-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_exp_energy_slope_right
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:02:36.805663+00:00
-- url     : https://prove2.me/submissions/8d91090a-ec82-4feb-b687-d571b0114afb

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
open scoped Topology
noncomputable section

/-- Right-hand Gaussian exponential energy slope at zero. -/
theorem solution
    (a : ℝ) :
    Filter.Tendsto (fun ε : ℝ => (Real.exp (a * ε) - 1) / ε)
      (𝓝[>] (0 : ℝ)) (𝓝 a) := by
  have hderiv :
      HasDerivAt (fun ε : ℝ => Real.exp (a * ε)) a (0 : ℝ) := by
    convert ((hasDerivAt_id (0 : ℝ)).const_mul a).exp using 1 <;> simp
  have hlim := hderiv.tendsto_slope_zero_right
  convert hlim using 1
  funext ε
  simp [div_eq_mul_inv, mul_comm]