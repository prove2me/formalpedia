-- Prove2me | solution 1 for DistanceGeometry.mem_sphereIntersection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:45:40.071451+00:00
-- url     : https://prove2.me/submissions/8974e4cb-fc9a-45a0-a466-4aeba6a168c9

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Basic
public import Definitions.Def_LeanPool_DistanceGeometry_Trilateration

set_option autoImplicit true
@[expose] public section
public section
open DistanceGeometry
open scoped RealInnerProductSpace
open EuclideanGeometry Module Submodule
variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P] [FiniteDimensional ℝ V]
  {ι : Type*} {c : ι → P} {r : ι → ℝ}
namespace DistanceGeometry
theorem _root_.solution {p : P} :
    p ∈ sphereIntersection c r ↔ ∀ i, dist p (c i) = r i := Iff.rfl
end DistanceGeometry
