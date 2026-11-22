-- Prove2me | solution 1 for Band.abs_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:29:53.171292+00:00
-- url     : https://prove2.me/submissions/f1669395-c6d9-4dd5-bd66-00a29cf5decb

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Ideal
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderComplete
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Band_Basic
public import Theorems.Thm_VectorSublattice_abs_mem


set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
open Band
variable (B : Band X)
namespace Band
theorem _root_.solution {x : X} (hx : x ∈ B) : |x| ∈ B :=
  B.toOrderIdeal.abs_mem hx
end Band
