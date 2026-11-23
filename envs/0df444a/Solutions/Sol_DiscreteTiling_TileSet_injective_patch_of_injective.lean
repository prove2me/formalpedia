-- Prove2me | solution 1 for DiscreteTiling.TileSet.injective_patch_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:21:07.802603+00:00
-- url     : https://prove2.me/submissions/d10ff5ac-f77b-4955-a751-46b08fee2722

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSetCard
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Patch
public import Theorems.Thm_DiscreteTiling_TileSet_injective_subtype_of_injective

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
theorem _root_.solution {t : TileSet ps ιₜ} (s : Set X) (ht : Injective t) :
    Injective (t.patch s) :=
  injective_subtype_of_injective _ ht
end DiscreteTiling.TileSet
