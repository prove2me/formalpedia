-- Prove2me | solution 1 for DiscreteTiling.TileSet.isohedralNumber_lt_aleph0_of_finite_quotient_tilePoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:11:07.748994+00:00
-- url     : https://prove2.me/submissions/beafc9b2-d4af-4719-b6b8-862a86c8d176

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Union
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.SetTheory.Cardinal.Finite
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Isohedral
public import Theorems.Thm_DiscreteTiling_TileSet_isohedralNumber_lt_aleph0_iff
public import Theorems.Thm_DiscreteTiling_TileSet_surjective_quotientPlacedTileOfquotientTilePoint

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
    (hf : Finite (MulAction.orbitRel.Quotient t.symmetryGroup
      {x : Prod (t : Set (PlacedTile ps)) X // x.2 ∈ (x.1 : PlacedTile ps)}))
    (hn : ∀ i, (t i : Set X).Nonempty) : t.isohedralNumber < ℵ₀ := by
  rw [isohedralNumber_lt_aleph0_iff]
  rw [← Set.finite_univ_iff] at hf ⊢
  exact Set.Finite.of_surjOn t.quotientPlacedTileOfquotientTilePoint
    (Set.surjOn_univ.2 (surjective_quotientPlacedTileOfquotientTilePoint hn)) hf
end DiscreteTiling.TileSet
