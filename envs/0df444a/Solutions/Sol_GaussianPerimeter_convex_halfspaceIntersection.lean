-- Prove2me | solution 1 for GaussianPerimeter.convex_halfspaceIntersection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:05:52.489803+00:00
-- url     : https://prove2.me/submissions/599d6425-8d70-4a1f-b2b1-d784e5268642

module
public import Definitions.Def_GaussianPerimeter_Definitions
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Definitions.Def_GaussianPerimeter_Geometry

set_option autoImplicit true
@[expose] public section
public section
open Function Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal InnerProductSpace RealInnerProductSpace Function
open GaussianPerimeter
local notation "Euc" k => EuclideanSpace ℝ (Fin k)
variable {k : ℕ} {ι : Type*}
namespace GaussianPerimeter
theorem _root_.solution (u : ι → Euc (k + 1)) (ρ : ℝ) :
    Convex ℝ (halfspaceIntersection u ρ) :=
  convex_iInter fun i =>
    (convex_Iic ρ).linear_preimage (innerSL ℝ (u i)).toLinearMap
end GaussianPerimeter
