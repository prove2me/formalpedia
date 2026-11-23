-- Prove2me | solution 1 for DiscreteTiling.TileSet.surjective_quotientPlacedTileOfquotientTilePoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:10:09.724716+00:00
-- url     : https://prove2.me/submissions/3def9cff-2a8d-461b-bfb8-a1757201ecde

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Union
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.SetTheory.Cardinal.Finite
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Isohedral
public import Theorems.Thm_DiscreteTiling_TileSet_apply_mem


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
theorem _root_.solution {t : TileSet ps ιₜ}
    (h : ∀ i, (t i : Set X).Nonempty) :
    Surjective t.quotientPlacedTileOfquotientTilePoint := by
  intro x
  induction x using Quotient.inductionOn' with
  | h pt =>
    rcases pt with ⟨pt, i, rfl⟩
    obtain ⟨x, hx⟩ := h i
    exact ⟨⟦⟨(⟨t i, apply_mem _ _⟩, x), hx⟩⟧, rfl⟩
end DiscreteTiling.TileSet
