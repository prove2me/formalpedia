-- Prove2me | solution 1 for DistanceGeometry.IsSqDistMatrix.eq_sqDistMatrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:46:08.050183+00:00
-- url     : https://prove2.me/submissions/7840edda-ea3f-4ea7-9215-a128c537e321

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
    {x : Fin n → EuclideanSpace ℝ (Fin k)} (hD : IsSqDistMatrix D x) :
    D = sqDistMatrix x :=
  Matrix.ext hD
end IsSqDistMatrix
end DistanceGeometry
