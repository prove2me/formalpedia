-- Prove2me | solution 1 for GaussianPerimeter.measurableSet_capCone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:10:42.907826+00:00
-- url     : https://prove2.me/submissions/a08f5ada-aa6a-4466-b3a6-6df607ea843b

module
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Constructions.Pi
public import Definitions.Def_GaussianPerimeter_Sphere

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set Function
open scoped ENNReal Pointwise RealInnerProductSpace
open GaussianPerimeter
local notation "UnitSphere" E => Metric.sphere (0 : E) 1
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [FiniteDimensional ℝ E]
namespace GaussianPerimeter
theorem _root_.solution (v : E) (t : ℝ) : MeasurableSet (capCone v t) := by
  have ha : MeasurableSet {x : E | 0 < ‖x‖} :=
    measurableSet_lt measurable_const continuous_norm.measurable
  have hb : MeasurableSet {x : E | ‖x‖ < 1} :=
    measurableSet_lt continuous_norm.measurable measurable_const
  have hc : MeasurableSet {x : E | t * ‖x‖ ≤ ⟪v, x⟫} :=
    measurableSet_le (by fun_prop) (by fun_prop)
  exact ha.inter (hb.inter hc)
end GaussianPerimeter
