-- Prove2me | solution 1 for DiscreteTiling.TileSet.aleph0_le_isohedralNumber_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:09:40.512784+00:00
-- url     : https://prove2.me/submissions/3cd2d692-48ae-4272-83cc-89f6f2f373a8

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Union
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.SetTheory.Cardinal.Finite
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Isohedral
public import Theorems.Thm_DiscreteTiling_TileSet_isohedralNumber_eq_card

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
theorem _root_.solution {t : TileSet ps ιₜ} :
    ℵ₀ ≤ t.isohedralNumber ↔
      Infinite (MulAction.orbitRel.Quotient t.symmetryGroup (t : Set (PlacedTile ps))) := by
  rw [Cardinal.infinite_iff, isohedralNumber_eq_card]
end DiscreteTiling.TileSet
