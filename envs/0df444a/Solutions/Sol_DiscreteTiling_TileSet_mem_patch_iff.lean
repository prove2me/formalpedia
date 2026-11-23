-- Prove2me | solution 1 for DiscreteTiling.TileSet.mem_patch_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:21:16.994795+00:00
-- url     : https://prove2.me/submissions/19866a2e-7fcf-4090-854a-61b9e273df8f

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSetCard
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Patch
public import Theorems.Thm_DiscreteTiling_TileSet_mem_subtype_iff
public import Theorems.Thm_DiscreteTiling_TileSet_mem_def


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
theorem _root_.solution {t : TileSet ps ιₜ} {s : Set X} {pt : PlacedTile ps} :
    pt ∈ t.patch s ↔ (s ∩ pt).Nonempty ∧ pt ∈ t := by
  rw [patch, mem_subtype_iff, TileSet.mem_def, ←exists_and_left]
  refine exists_congr fun i ↦ ?_
  rw [and_congr_left_iff]
  rintro rfl
  rfl
end DiscreteTiling.TileSet
