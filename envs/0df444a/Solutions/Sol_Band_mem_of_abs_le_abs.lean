-- Prove2me | solution 1 for Band.mem_of_abs_le_abs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:30:04.669627+00:00
-- url     : https://prove2.me/submissions/a26c2be9-5472-4eb3-8a8c-d4068cf1e715

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Ideal
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderComplete
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Band_Basic
public import Theorems.Thm_OrderIdeal_mem_of_abs_le_abs


set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
open Band
variable (B : Band X)
namespace Band
theorem _root_.solution {x y : X} (hx : x ∈ B) (h : |y| ≤ |x|) :
    y ∈ B :=
  B.toOrderIdeal.mem_of_abs_le_abs hx h
end Band
