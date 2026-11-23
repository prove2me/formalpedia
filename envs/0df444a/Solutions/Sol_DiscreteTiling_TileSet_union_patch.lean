-- Prove2me | solution 1 for DiscreteTiling.TileSet.union_patch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:21:23.729874+00:00
-- url     : https://prove2.me/submissions/4b317bff-0a39-487c-9407-85121771c0af

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSetCard
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Patch
public import Theorems.Thm_DiscreteTiling_TileSet_union_subtype

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
    ⋃ i, (t.patch s i : Set X) = ⋃ (i) (_ : (s ∩ t i).Nonempty), (t i : Set X) :=
  t.union_subtype _
end DiscreteTiling.TileSet
