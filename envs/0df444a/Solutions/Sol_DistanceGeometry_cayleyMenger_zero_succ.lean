-- Prove2me | solution 1 for DistanceGeometry.cayleyMenger_zero_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:46:04.22959+00:00
-- url     : https://prove2.me/submissions/522e00e3-a567-41c3-8d70-6c129840fbf3

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
    (j : Fin (n + 1)) : cayleyMenger D 0 j.succ = 1 := rfl
end DistanceGeometry
