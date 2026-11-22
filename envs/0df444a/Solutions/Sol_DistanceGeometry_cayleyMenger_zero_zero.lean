-- Prove2me | solution 1 for DistanceGeometry.cayleyMenger_zero_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:46:03.764937+00:00
-- url     : https://prove2.me/submissions/3eacdd7e-fb12-4d8c-a14c-9bad25ccb5ef

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
theorem _root_.solution (D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    cayleyMenger D 0 0 = 0 := rfl
end DistanceGeometry
