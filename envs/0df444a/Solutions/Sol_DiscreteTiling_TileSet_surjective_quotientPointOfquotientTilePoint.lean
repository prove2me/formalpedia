-- Prove2me | solution 1 for DiscreteTiling.TileSet.surjective_quotientPointOfquotientTilePoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:10:12.621824+00:00
-- url     : https://prove2.me/submissions/3f19dc4f-8e48-4865-b8a6-a7dc3a481539

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Union
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.SetTheory.Cardinal.Finite
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Isohedral
public import Theorems.Thm_DiscreteTiling_TileSet_UnionEqUniv_exists_mem_mem


set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open DiscreteTiling
open Function
open scoped Cardinal Pointwise
variable {G X ιₚ ιₜ : Type*} [Group G] [MulAction G X] {ps : Protoset G X ιₚ}
open DiscreteTiling.TileSet
namespace DiscreteTiling.TileSet
theorem _root_.solution {t : TileSet ps ιₜ} (h : t.UnionEqUniv) :
    Surjective t.quotientPointOfquotientTilePoint := by
  intro x
  induction x using Quotient.inductionOn' with
  | h p =>
    obtain ⟨pt, hpt, hp⟩ := UnionEqUniv.exists_mem_mem h p
    exact ⟨⟦⟨(⟨pt, hpt⟩, p), hp⟩⟧, rfl⟩
end DiscreteTiling.TileSet
