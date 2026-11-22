-- Prove2me | solution 1 for DistanceGeometry.cayleyMenger_succ_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:46:14.269309+00:00
-- url     : https://prove2.me/submissions/514f7967-848f-4432-8254-dda22fc3aaca

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
    (i : Fin (n + 1)) : cayleyMenger D i.succ 0 = 1 := rfl
end DistanceGeometry
