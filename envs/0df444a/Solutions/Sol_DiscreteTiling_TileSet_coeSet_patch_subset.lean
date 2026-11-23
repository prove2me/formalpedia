-- Prove2me | solution 1 for DiscreteTiling.TileSet.coeSet_patch_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:21:13.339496+00:00
-- url     : https://prove2.me/submissions/9bb11746-5663-4017-beb7-03052e98759c

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSetCard
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Patch
public import Theorems.Thm_DiscreteTiling_TileSet_coeSet_subtype_subset

set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open DiscreteTiling
open Function
open scoped Cardinal Pointwise
variable {G X ιₚ ιₜ ιₜ' Eᵤ : Type*} [Group G] [MulAction G X] {ps : Protoset G X ιₚ}
universe u
variable {ιᵤ ιᵤ' : Type u} [EquivLike Eᵤ ιᵤ' ιᵤ]
open DiscreteTiling.TileSet
namespace DiscreteTiling.TileSet
theorem _root_.solution (t : TileSet ps ιₜ) (s : Set X) :
    (t.patch s : Set (PlacedTile ps)) ⊆ t :=
  t.coeSet_subtype_subset _
end DiscreteTiling.TileSet
