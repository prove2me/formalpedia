-- Prove2me | solution 1 for DiscreteTiling.TileSet.coeSet_subtype
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:13:38.360809+00:00
-- url     : https://prove2.me/submissions/a0a2e5e7-f119-4197-bed6-9347b41c1fe2

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSetCard
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Patch
public import Theorems.Thm_DiscreteTiling_TileSet_coeSet_reindex_eq_range_comp


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
theorem _root_.solution (t : TileSet ps ιₜ) (p : ιₜ → Prop) : t.subtype p = t '' {i | p i} := by
  rw [TileSet.subtype, coeSet_reindex_eq_range_comp, Set.range_comp, Subtype.range_coe_subtype]
end DiscreteTiling.TileSet
