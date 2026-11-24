-- Prove2me | solution 1 for GaussianPerimeter.radialDensity_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:25:57.701298+00:00
-- url     : https://prove2.me/submissions/2a3d6f12-f8ba-4e63-9d85-644deb950bf8

module
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_GaussianPerimeter_Radial
public import Theorems.Thm_GaussianPerimeter_radialKernel_integrable

set_option autoImplicit true
@[expose] public section
public section
open Filter MeasureTheory Set
open scoped Topology
open GaussianPerimeter
namespace GaussianPerimeter
theorem _root_.solution (n : ℕ) : Integrable (radialDensity n) := by
  change Integrable (fun r : ℝ => radialKernel n r / (∫ t : ℝ, radialKernel n t))
  simpa only [div_eq_mul_inv] using
    (radialKernel_integrable n).mul_const (∫ r : ℝ, radialKernel n r)⁻¹
end GaussianPerimeter
