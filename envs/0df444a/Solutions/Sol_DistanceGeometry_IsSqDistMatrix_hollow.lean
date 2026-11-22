-- Prove2me | solution 1 for DistanceGeometry.IsSqDistMatrix.hollow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:46:07.031653+00:00
-- url     : https://prove2.me/submissions/fe9f6934-db59-4cda-876c-1ee62ae94b9e

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Definitions.Def_LeanPool_DistanceGeometry_Defs
public import Theorems.Thm_DistanceGeometry_sqDistMatrix_apply
attribute [local simp] DistanceGeometry.sqDistMatrix_apply

set_option autoImplicit true
@[expose] public section
public section
open DistanceGeometry
open scoped RealInnerProductSpace
variable {n k : ℕ}
namespace DistanceGeometry
namespace IsSqDistMatrix
theorem _root_.solution {D : Matrix (Fin n) (Fin n) ℝ}
    {x : Fin n → EuclideanSpace ℝ (Fin k)} (hD : IsSqDistMatrix D x) (i : Fin n) :
    D i i = 0 := by
  rw [hD i i, dist_self]; simp
end IsSqDistMatrix
end DistanceGeometry
