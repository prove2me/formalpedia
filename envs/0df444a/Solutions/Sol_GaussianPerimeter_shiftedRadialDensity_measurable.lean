-- Prove2me | solution 1 for GaussianPerimeter.shiftedRadialDensity_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:23:55.386952+00:00
-- url     : https://prove2.me/submissions/a4ba1075-d50c-4456-afad-3965f06e503c

module
public import Definitions.Def_GaussianPerimeter_LimitBound
public import Definitions.Def_GaussianPerimeter_CapAsymptotics
public import Definitions.Def_GaussianPerimeter_Radial
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Definitions.Def_GaussianPerimeter_NazarovLimit
public import Theorems.Thm_GaussianPerimeter_radialDensity_measurable


set_option autoImplicit true
@[expose] public section
public section
open Filter MeasureTheory
open scoped ENNReal Topology
open GaussianPerimeter
namespace GaussianPerimeter
theorem _root_.solution (n : ℕ) : Measurable (shiftedRadialDensity n) :=
  (radialDensity_measurable n).comp (by fun_prop)
end GaussianPerimeter
