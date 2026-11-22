-- Prove2me | solution 1 for DistanceGeometry.IsPreDistMatrix.symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:45:38.408091+00:00
-- url     : https://prove2.me/submissions/1d7ce3d0-b661-4796-8f12-b91430a2024d

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
namespace IsPreDistMatrix
theorem _root_.solution {D : Matrix (Fin n) (Fin n) ℝ} (hD : IsPreDistMatrix D)
    (i j : Fin n) : D i j = D j i := hD.1 i j
end IsPreDistMatrix
end DistanceGeometry
