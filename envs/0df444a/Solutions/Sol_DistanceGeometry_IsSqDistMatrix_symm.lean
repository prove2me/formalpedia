-- Prove2me | solution 1 for DistanceGeometry.IsSqDistMatrix.symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:45:29.454003+00:00
-- url     : https://prove2.me/submissions/3a2b9418-b11b-47ee-85a0-4da40a657a49

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
namespace IsSqDistMatrix
theorem _root_.solution {D : Matrix (Fin n) (Fin n) ℝ}
    {x : Fin n → EuclideanSpace ℝ (Fin k)} (hD : IsSqDistMatrix D x) (i j : Fin n) :
    D i j = D j i := by
  rw [hD i j, hD j i, dist_comm]
end IsSqDistMatrix
end DistanceGeometry
