-- Prove2me | solution 1 for DiscreteTiling.TileSet.isTilingOf_iff_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:22:32.827585+00:00
-- url     : https://prove2.me/submissions/fd3d29ba-83a7-4f08-b46a-e06e545d0e90

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Union
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Tiling
public import Theorems.Thm_DiscreteTiling_TileSet_isTilingOf_iff
public import Theorems.Thm_DiscreteTiling_TileSet_coeSet_disjoint_iff_disjoint_of_injective
public import Theorems.Thm_DiscreteTiling_TileSet_union_of_mem_eq_iUnion


set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open DiscreteTiling
open Function
open scoped Pointwise
variable {G X ιₚ : Type*} [Group G] [MulAction G X]
variable {ps : Protoset G X ιₚ} {ιₜ : Type*}
open DiscreteTiling.TileSet
namespace DiscreteTiling.TileSet
theorem _root_.solution {t : TileSet ps ιₜ} {s : Set X} (h : Injective t) :
    t.IsTilingOf s ↔ ((t : Set (PlacedTile ps)).Pairwise fun x y ↦ Disjoint (x : Set X) y) ∧
      (⋃ pt ∈ t, (pt : Set X)) = s := by
  rw [isTilingOf_iff, ← TileSet.disjoint_iff, ← coeSet_disjoint_iff_disjoint_of_injective h,
    union_of_mem_eq_iUnion]
end DiscreteTiling.TileSet
