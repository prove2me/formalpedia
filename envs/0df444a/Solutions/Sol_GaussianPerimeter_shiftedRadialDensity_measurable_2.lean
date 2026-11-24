-- Prove2me | solution 2 for GaussianPerimeter.shiftedRadialDensity_measurable
-- status  : ACCEPTED   (prove)
-- author  : @bbchallenge_user
-- created : 2026-11-24T11:24:44.197194+00:00
-- url     : https://prove2.me/submissions/af8c9b75-f51b-44eb-983f-7162aa328727

module
public import Definitions.Def_GaussianPerimeter_LimitBound
public import Definitions.Def_GaussianPerimeter_CapAsymptotics
public import Definitions.Def_GaussianPerimeter_Radial
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Definitions.Def_GaussianPerimeter_NazarovLimit
set_option autoImplicit true
@[expose] public section
public section
open Filter MeasureTheory
open scoped ENNReal Topology
open GaussianPerimeter

theorem solution (n : ℕ) : Measurable (shiftedRadialDensity n) := by
  have hk : Measurable (radialKernel n) := by
    unfold radialKernel
    exact (by fun_prop : Measurable fun r : ℝ => r ^ (n - 1) * Real.exp (-r ^ 2 / 2)).indicator
      measurableSet_Ioi
  unfold shiftedRadialDensity radialDensity
  exact (hk.comp (measurable_const.add measurable_id)).div_const _
