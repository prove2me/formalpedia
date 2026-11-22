-- Prove2me | solution 1 for Band.solid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:29:59.101092+00:00
-- url     : https://prove2.me/submissions/fdb4f9a1-12fb-4fa8-ad15-1f5f35baae30

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Ideal
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderComplete
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Band_Basic

set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
open Band
variable (B : Band X)
namespace Band
theorem _root_.solution {x y : X} (hx : x ∈ B) (hy0 : 0 ≤ y) (hyx : y ≤ x) :
    y ∈ B :=
  B.toOrderIdeal.solid hx hy0 hyx
end Band
