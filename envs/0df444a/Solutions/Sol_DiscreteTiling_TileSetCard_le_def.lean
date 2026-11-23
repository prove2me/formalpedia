-- Prove2me | solution 1 for DiscreteTiling.TileSetCard.le_def
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T05:56:15.098809+00:00
-- url     : https://prove2.me/submissions/dd55c14a-b830-4038-bf5c-a844478089cb

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
theorem _root_.solution {t₁ t₂ : TileSetCard ps} : t₁ ≤ t₂ ↔ ∀ i, t₁ i ≤ t₂ i :=
  Iff.rfl
end DiscreteTiling.TileSetCard
