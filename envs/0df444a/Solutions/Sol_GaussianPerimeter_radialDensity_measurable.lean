-- Prove2me | solution 1 for GaussianPerimeter.radialDensity_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:36:02.363016+00:00
-- url     : https://prove2.me/submissions/2354e8e5-b8fb-42d1-af03-9f1e47b891a4

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
theorem _root_.solution (n : ℕ) : Measurable (radialDensity n) := by
  have h : Measurable (radialKernel n) := by
    unfold radialKernel
    apply Measurable.indicator _ measurableSet_Ioi
    fun_prop
  exact h.div measurable_const
end GaussianPerimeter
