-- Prove2me | solution 1 for DistanceGeometry.IsPreDistMatrix.hollow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:45:29.901256+00:00
-- url     : https://prove2.me/submissions/b49ac4aa-edbd-4fac-a49a-4480798916f0

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
    (i : Fin n) : D i i = 0 := hD.2 i
end IsPreDistMatrix
end DistanceGeometry
