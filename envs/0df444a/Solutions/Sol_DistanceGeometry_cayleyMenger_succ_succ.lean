-- Prove2me | solution 1 for DistanceGeometry.cayleyMenger_succ_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:46:14.963343+00:00
-- url     : https://prove2.me/submissions/8dd3b9ce-b263-4c15-8d3d-73d65019fea5

module
public import Definitions.Def_LeanPool_DistanceGeometry_Defs
public import Definitions.Def_LeanPool_DistanceGeometry_Schoenberg
public import Definitions.Def_LeanPool_DistanceGeometry_CayleyMengerVolume

set_option autoImplicit true
@[expose] public section
public section
open DistanceGeometry
open Matrix
open scoped RealInnerProductSpace
variable {n : ℕ}
namespace DistanceGeometry
theorem _root_.solution (D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (i j : Fin (n + 1)) : cayleyMenger D i.succ j.succ = D i j := rfl
end DistanceGeometry
