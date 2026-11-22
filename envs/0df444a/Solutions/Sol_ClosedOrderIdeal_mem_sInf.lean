-- Prove2me | solution 1 for ClosedOrderIdeal.mem_sInf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:27:22.100792+00:00
-- url     : https://prove2.me/submissions/1a227c8a-a7db-493d-8308-d9abd42f28f1

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
theorem _root_.solution {S : Set (ClosedOrderIdeal X)} {x : X} :
    x ∈ (InfSet.sInf S : ClosedOrderIdeal X) ↔ ∀ J ∈ S, x ∈ J := by
  change x ∈ (InfSet.sInf ((fun J : ClosedOrderIdeal X => J.toOrderIdeal) '' S) : OrderIdeal X) ↔ _
  rw [OrderIdeal.mem_sInf]
  refine ⟨fun h J hJ => h _ ⟨J, hJ, rfl⟩, ?_⟩
  rintro h _ ⟨J, hJ, rfl⟩; exact h J hJ
end ClosedOrderIdeal
