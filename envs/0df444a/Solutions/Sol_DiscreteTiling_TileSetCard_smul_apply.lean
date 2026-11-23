-- Prove2me | solution 1 for DiscreteTiling.TileSetCard.smul_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:02:32.934058+00:00
-- url     : https://prove2.me/submissions/46f0fb75-583a-429f-901e-4bf73add3bb6

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
theorem _root_.solution (g : G) (t : TileSetCard ps) (pt : PlacedTile ps) : (g • t) pt = t (g⁻¹ • pt) :=
  rfl
end DiscreteTiling.TileSetCard
