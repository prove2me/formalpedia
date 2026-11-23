-- Prove2me | solution 1 for DiscreteTiling.TileSet.card_patch_apply_of_inter_eq_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:15:02.633941+00:00
-- url     : https://prove2.me/submissions/c8ff4a41-2717-43b2-8179-479605212669

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSetCard
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Patch
public import Theorems.Thm_DiscreteTiling_TileSetFunction_toVarTileSetFunction_apply
public import Theorems.Thm_DiscreteTiling_TileSetFunction_toVarTileSetFunction_const
public import Theorems.Thm_DiscreteTiling_TileSetFunction_toVarTileSetFunction_toTileSetFunction
public import Theorems.Thm_DiscreteTiling_TileSet_card_apply
public import Theorems.Thm_DiscreteTiling_TileSet_card_reindex_of_equivLike
public import Theorems.Thm_DiscreteTiling_TileSet_coeSet_sigma
public import Theorems.Thm_DiscreteTiling_TileSet_coeSet_sum
public import Theorems.Thm_DiscreteTiling_TileSet_coe_sigma
public import Theorems.Thm_DiscreteTiling_TileSet_coe_sum
public import Theorems.Thm_DiscreteTiling_TileSet_finiteDistinctIntersectionsOn_empty
public import Theorems.Thm_DiscreteTiling_TileSet_finiteDistinctIntersectionsOn_of_subsingleton
public import Theorems.Thm_DiscreteTiling_TileSet_finiteDistinctIntersectionsOn_univ_iff
public import Theorems.Thm_DiscreteTiling_TileSet_mem_sum
public import Theorems.Thm_DiscreteTiling_TileSet_smul_prod_one
public import Theorems.Thm_DiscreteTiling_TileSet_smul_prod_refl
public import Theorems.Thm_DiscreteTiling_TileSet_symmetryGroup_of_isEmpty
public import Theorems.Thm_DiscreteTiling_TileSet_symmetryGroup_reindex
public import Theorems.Thm_DiscreteTiling_TileSet_symmetryGroup_reindex_of_bijective
attribute [local simp] DiscreteTiling.TileSet.card_reindex_of_equivLike
attribute [local simp] DiscreteTiling.TileSet.coeSet_sigma
attribute [local simp] DiscreteTiling.TileSet.coeSet_sum
attribute [local simp] DiscreteTiling.TileSet.coe_sigma
attribute [local simp] DiscreteTiling.TileSet.coe_sum
attribute [local simp] DiscreteTiling.TileSet.finiteDistinctIntersectionsOn_empty
attribute [local simp] DiscreteTiling.TileSet.finiteDistinctIntersectionsOn_of_subsingleton
attribute [local simp] DiscreteTiling.TileSet.finiteDistinctIntersectionsOn_univ_iff
attribute [local simp] DiscreteTiling.TileSet.mem_sum
attribute [local simp] DiscreteTiling.TileSet.smul_prod_one
attribute [local simp] DiscreteTiling.TileSet.smul_prod_refl
attribute [local simp] DiscreteTiling.TileSet.symmetryGroup_of_isEmpty
attribute [local simp] DiscreteTiling.TileSet.symmetryGroup_reindex
attribute [local simp] DiscreteTiling.TileSet.symmetryGroup_reindex_of_bijective
attribute [local simp] DiscreteTiling.TileSetFunction.toVarTileSetFunction_apply
attribute [local simp] DiscreteTiling.TileSetFunction.toVarTileSetFunction_const
attribute [local simp] DiscreteTiling.TileSetFunction.toVarTileSetFunction_toTileSetFunction



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
theorem _root_.solution (t : TileSet ps ιₜ) {s : Set X} {pt : PlacedTile ps}
    (h : (s ∩ pt) = ∅) : (t.patch s).card pt = 0 := by
  rw [card_apply, Cardinal.mk_eq_zero_iff]
  simp only [coe_patch, isEmpty_subtype, Set.mem_preimage, comp_apply, Set.mem_singleton_iff,
             Subtype.forall]
  rintro i hne rfl
  simp [h] at hne
end DiscreteTiling.TileSet
