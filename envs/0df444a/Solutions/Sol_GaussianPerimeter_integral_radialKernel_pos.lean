-- Prove2me | solution 1 for GaussianPerimeter.integral_radialKernel_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:46:45.588392+00:00
-- url     : https://prove2.me/submissions/21d1695d-5ec4-44e8-9b7b-70be16e74b73

module
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_GaussianPerimeter_Radial
public import Theorems.Thm_GaussianPerimeter_integral_radialKernel

set_option autoImplicit true
@[expose] public section
public section
open Filter MeasureTheory Set
open scoped Topology
open GaussianPerimeter
namespace GaussianPerimeter
theorem _root_.solution (n : ℕ) (hn : 0 < n) :
    0 < ∫ r : ℝ, radialKernel n r := by
  rw [integral_radialKernel n hn]
  exact mul_pos (by positivity) (Real.Gamma_pos_of_pos (by positivity))
end GaussianPerimeter
