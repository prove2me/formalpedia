-- Prove2me | solution 1 for GaussianPerimeter.radialKernel_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @bbchallenge_user
-- created : 2026-11-24T11:17:46.026843+00:00
-- url     : https://prove2.me/submissions/9dfafe3f-7118-43e8-a9ef-007aee10b950

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

theorem solution (n : ℕ) (r : ℝ) : 0 ≤ radialKernel n r := by
  unfold radialKernel
  apply Set.indicator_nonneg
  intro t ht
  have : 0 < t := ht
  positivity
