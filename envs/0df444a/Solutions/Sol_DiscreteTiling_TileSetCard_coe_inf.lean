-- Prove2me | solution 1 for DiscreteTiling.TileSetCard.coe_inf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:20:37.505871+00:00
-- url     : https://prove2.me/submissions/29e00914-d093-4fa7-a707-9511e58c0442

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSet
public import Mathlib.SetTheory.Cardinal.Basic
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSetCard

set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open DiscreteTiling
open Function
open scoped Cardinal Pointwise
variable {G X ιₚ : Type*} [Group G] [MulAction G X]
variable {ps : Protoset G X ιₚ} {ιₜ E F : Type*}
universe u v
variable {ιᵤ ιᵤ' : Type u} [EquivLike E ιᵤ' ιᵤ] [FunLike F ιᵤ' ιᵤ] [EmbeddingLike F ιᵤ' ιᵤ]
open DiscreteTiling.TileSetCard
attribute [coe] tilesCard
namespace DiscreteTiling.TileSetCard
theorem _root_.solution (t₁ t₂ : TileSetCard ps) :
    (t₁ ⊓ t₂ : TileSetCard ps) = (t₁ : PlacedTile ps → Cardinal) ⊓ ↑t₂ :=
  rfl
end DiscreteTiling.TileSetCard
