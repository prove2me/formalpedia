-- Prove2me | solution 1 for ClosedOrderIdeal.inf_toSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:27:22.609245+00:00
-- url     : https://prove2.me/submissions/774c0441-6876-4ea7-b81f-d13789dfceab

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Sublattice
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderUnit
public import Mathlib.Analysis.Normed.Group.Completeness
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Ideal

set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
open ClosedOrderIdeal
variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [BanachLattice X]
namespace ClosedOrderIdeal
theorem _root_.solution (J₁ J₂ : ClosedOrderIdeal X) :
    (J₁ ⊓ J₂).toSubmodule = J₁.toSubmodule ⊓ J₂.toSubmodule := rfl
end ClosedOrderIdeal
