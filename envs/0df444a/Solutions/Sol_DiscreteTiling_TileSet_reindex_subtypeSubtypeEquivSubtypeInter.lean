-- Prove2me | solution 1 for DiscreteTiling.TileSet.reindex_subtypeSubtypeEquivSubtypeInter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:21:07.136496+00:00
-- url     : https://prove2.me/submissions/6ddd0aaf-6a20-4858-bea0-b3954e31a4d2

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSetCard
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Patch

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
theorem _root_.solution (t : TileSet ps ιₜ) (p q : ιₜ → Prop) :
    (t.subtype (fun i ↦ p i ∧ q i)).reindex (Equiv.subtypeSubtypeEquivSubtypeInter p q) =
      (t.subtype p).subtype (q ∘ Subtype.val) :=
  rfl
end DiscreteTiling.TileSet
