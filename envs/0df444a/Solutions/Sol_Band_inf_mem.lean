-- Prove2me | solution 1 for Band.inf_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:29:44.160805+00:00
-- url     : https://prove2.me/submissions/01017336-1d36-404e-b706-8dda37f30743

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
theorem _root_.solution {x y : X} (hx : x ∈ B) (hy : y ∈ B) :
    x ⊓ y ∈ B :=
  B.toOrderIdeal.inf_mem hx hy
end Band
