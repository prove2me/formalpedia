-- Prove2me | solution 1 for DiscreteTiling.TileSet.finite_preimage_quotientPlacedTileOfquotientTilePoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:11:42.5824+00:00
-- url     : https://prove2.me/submissions/b6820801-713d-43d5-8802-86d03b0586b2

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Union
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.SetTheory.Cardinal.Finite
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Isohedral
public import Theorems.Thm_DiscreteTiling_TileSet_preimage_quotientPlacedTileOfquotientTilePoint_eq_range

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
    {pt : (t : Set (PlacedTile ps))} (h : ((pt : PlacedTile ps) : Set X).Finite) :
    (t.quotientPlacedTileOfquotientTilePoint ⁻¹' {⟦pt⟧}).Finite := by
  have := h.to_subtype
  rw [preimage_quotientPlacedTileOfquotientTilePoint_eq_range]
  exact Set.finite_range _
end DiscreteTiling.TileSet
