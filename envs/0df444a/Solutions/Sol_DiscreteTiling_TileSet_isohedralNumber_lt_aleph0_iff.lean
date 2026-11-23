-- Prove2me | solution 1 for DiscreteTiling.TileSet.isohedralNumber_lt_aleph0_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:05:50.048131+00:00
-- url     : https://prove2.me/submissions/2cccaf79-3ae6-40e9-8dcc-c20a76defbed

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
    t.isohedralNumber < ℵ₀ ↔
      Finite (MulAction.orbitRel.Quotient t.symmetryGroup (t : Set (PlacedTile ps))) := by
  rw [isohedralNumber_eq_card, Cardinal.lt_aleph0_iff_finite]
end DiscreteTiling.TileSet
