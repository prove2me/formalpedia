-- Prove2me | solution 1 for DistanceGeometry.IsSqDistMatrix.isPreDistMatrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:46:43.728728+00:00
-- url     : https://prove2.me/submissions/8042259f-3902-4e9d-9fe0-3b165423b4ed

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Definitions.Def_LeanPool_DistanceGeometry_Defs
public import Theorems.Thm_DistanceGeometry_IsSqDistMatrix_symm
public import Theorems.Thm_DistanceGeometry_IsSqDistMatrix_hollow
public import Theorems.Thm_DistanceGeometry_IsPreDistMatrix_symm
public import Theorems.Thm_DistanceGeometry_IsPreDistMatrix_hollow

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
    IsPreDistMatrix D :=
  ⟨hD.symm, hD.hollow⟩
end IsSqDistMatrix
end DistanceGeometry
