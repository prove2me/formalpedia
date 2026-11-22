-- Prove2me | solution 1 for DistanceGeometry.sqDistMatrix_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:45:28.025938+00:00
-- url     : https://prove2.me/submissions/5981d1be-c9f9-47a8-aabb-308b83e00572

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Definitions.Def_LeanPool_DistanceGeometry_Defs

set_option autoImplicit true
@[expose] public section
public section
open DistanceGeometry
open scoped RealInnerProductSpace
variable {n k : ℕ}
namespace DistanceGeometry
theorem _root_.solution (x : Fin n → EuclideanSpace ℝ (Fin k)) (i j : Fin n) :
    sqDistMatrix x i j = dist (x i) (x j) ^ 2 := rfl
end DistanceGeometry
