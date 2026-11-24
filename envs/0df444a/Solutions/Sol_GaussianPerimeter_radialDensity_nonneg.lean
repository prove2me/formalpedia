-- Prove2me | solution 1 for GaussianPerimeter.radialDensity_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @bbchallenge_user
-- created : 2026-11-24T11:17:46.6994+00:00
-- url     : https://prove2.me/submissions/482089b2-71e7-466e-8837-8a7c70f9b9f9

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

theorem solution (n : ℕ) (r : ℝ) : 0 ≤ radialDensity n r := by
  have hk : ∀ t : ℝ, 0 ≤ radialKernel n t := by
    intro t
    unfold radialKernel
    apply Set.indicator_nonneg
    intro u hu
    have : 0 < u := hu
    positivity
  unfold radialDensity
  exact div_nonneg (hk r) (integral_nonneg hk)
