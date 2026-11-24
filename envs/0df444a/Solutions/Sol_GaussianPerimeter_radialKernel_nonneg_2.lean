-- Prove2me | solution 2 for GaussianPerimeter.radialKernel_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:23:24.175683+00:00
-- url     : https://prove2.me/submissions/2e68d354-cba9-46b2-b2f1-0f3f67f70054

module
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_GaussianPerimeter_Radial

set_option autoImplicit true
@[expose] public section
public section
open Filter MeasureTheory Set
open scoped Topology
open GaussianPerimeter
namespace GaussianPerimeter
theorem _root_.solution (n : ℕ) (r : ℝ) : 0 ≤ radialKernel n r := by
  classical
  unfold radialKernel
  by_cases hr : r ∈ Ioi (0 : ℝ)
  · rw [indicator_of_mem hr]
    exact mul_nonneg (pow_nonneg (le_of_lt (show 0 < r from hr)) _) (Real.exp_pos _).le
  · rw [indicator_of_notMem hr]
end GaussianPerimeter
