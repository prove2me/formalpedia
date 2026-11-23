-- Prove2me | solution 1 for DiscreteTiling.TileSet.finite_quotient_tilePoint_of_isohedralNumber_lt_aleph0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:17:13.564812+00:00
-- url     : https://prove2.me/submissions/4013f65a-5fdf-46a1-9d45-aa69d64861c8

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Union
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.SetTheory.Cardinal.Finite
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Isohedral
public import Theorems.Thm_DiscreteTiling_TileSet_isohedralNumber_lt_aleph0_iff
public import Theorems.Thm_DiscreteTiling_TileSet_finite_preimage_quotientPlacedTileOfquotientTilePoint

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
    (h : t.isohedralNumber < ℵ₀) (hf : ∀ i, (t i : Set X).Finite) :
    Finite (MulAction.orbitRel.Quotient t.symmetryGroup
      {x : Prod (t : Set (PlacedTile ps)) X // x.2 ∈ (x.1 : PlacedTile ps)}) := by
  rw [← Set.finite_univ_iff, ← Set.preimage_univ (f := t.quotientPlacedTileOfquotientTilePoint),
    ← Set.biUnion_preimage_singleton]
  rw [isohedralNumber_lt_aleph0_iff] at h
  refine Finite.Set.finite_biUnion _ _ fun pt _ ↦ ?_
  induction pt using Quotient.inductionOn' with
  | h pt =>
    rw [@Quotient.mk''_eq_mk]
    refine finite_preimage_quotientPlacedTileOfquotientTilePoint ?_
    rcases pt with ⟨pt, i, rfl⟩
    exact hf i
end DiscreteTiling.TileSet
