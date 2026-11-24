-- Prove2me | solution 1 for GaussianPerimeter.measurableSet_strictFacet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:08:44.530684+00:00
-- url     : https://prove2.me/submissions/926d5551-47b6-42c1-9e19-58e00d3e4b17

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
theorem _root_.solution [Countable ι] (u : ι → Euc (k + 1)) (ρ : ℝ) (i : ι) :
    MeasurableSet (strictFacet u ρ i) :=
  (isClosed_eq (innerSL ℝ (u i)).continuous continuous_const).measurableSet.inter <|
    MeasurableSet.iInter fun j =>
      (isOpen_lt (innerSL ℝ (u j.1)).continuous continuous_const).measurableSet
end GaussianPerimeter
