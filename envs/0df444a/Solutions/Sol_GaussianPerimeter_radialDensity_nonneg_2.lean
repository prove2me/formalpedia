-- Prove2me | solution 2 for GaussianPerimeter.radialDensity_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:24:00.332838+00:00
-- url     : https://prove2.me/submissions/b667ccea-0390-47f3-a6f8-399b10bee580

module
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_GaussianPerimeter_Radial
public import Theorems.Thm_GaussianPerimeter_radialKernel_nonneg

set_option autoImplicit true
@[expose] public section
public section
open Filter MeasureTheory Set
open scoped Topology
open GaussianPerimeter
namespace GaussianPerimeter
theorem _root_.solution (n : ℕ) (r : ℝ) : 0 ≤ radialDensity n r :=
  div_nonneg (radialKernel_nonneg n r) (integral_nonneg (radialKernel_nonneg n))
end GaussianPerimeter
