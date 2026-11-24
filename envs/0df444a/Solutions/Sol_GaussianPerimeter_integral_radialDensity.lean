-- Prove2me | solution 1 for GaussianPerimeter.integral_radialDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:26:32.736057+00:00
-- url     : https://prove2.me/submissions/b65aae15-fc6e-4a56-8d08-0b00fa2f52be

module
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_GaussianPerimeter_Radial
public import Theorems.Thm_GaussianPerimeter_integral_radialKernel_pos

set_option autoImplicit true
@[expose] public section
public section
open Filter MeasureTheory Set
open scoped Topology
open GaussianPerimeter
namespace GaussianPerimeter
theorem _root_.solution (n : ℕ) (hn : 0 < n) :
    (∫ r : ℝ, radialDensity n r) = 1 := by
  simp_rw [radialDensity, div_eq_mul_inv, integral_mul_const]
  exact mul_inv_cancel₀ (integral_radialKernel_pos n hn).ne'
end GaussianPerimeter
