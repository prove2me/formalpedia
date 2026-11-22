-- Prove2me | solution 1 for BanachLattice.isOrderContinuousNorm_iff_disjoint_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:20:58.679971+00:00
-- url     : https://prove2.me/submissions/7a6c603f-9f9e-4370-adb7-b402e44e1396

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderContinuous_Nakano
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderContinuous_MeyerNieberg
public import Theorems.Thm_BanachLattice_disjoint_bddAbove_tendsto_zero
public import Theorems.Thm_BanachLattice_isOrderContinuousNorm_of_disjoint_tendsto_zero

set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
open BanachLattice
variable [BanachLattice X]
namespace BanachLattice
theorem _root_.solution :
    IsOrderContinuousNorm X ↔
      (∀ {u : ℕ → X},
        Pairwise (fun i j => IsVLDisjoint (u i) (u j)) →
        BddAbove (Set.range fun n => |u n|) →
        Filter.Tendsto u Filter.atTop (nhds 0)) :=
  ⟨fun _ => disjoint_bddAbove_tendsto_zero,
   fun h => isOrderContinuousNorm_of_disjoint_tendsto_zero (fun hd hbd => h hd hbd)⟩
end BanachLattice
