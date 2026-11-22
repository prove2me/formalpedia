-- Prove2me | solution 1 for Band.mem_of_abs_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:29:53.742221+00:00
-- url     : https://prove2.me/submissions/2cc63e20-e5b7-4192-88bb-e370d010e4f6

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
theorem _root_.solution {x : X} (h : |x| ∈ B) : x ∈ B :=
  B.toOrderIdeal.mem_of_abs_mem h
end Band
