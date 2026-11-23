-- Prove2me | solution 1 for DiscreteTiling.TileSet.finite_preimage_quotientPointOfquotientTilePoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:12:14.981619+00:00
-- url     : https://prove2.me/submissions/90235383-4dbc-489b-8946-2a49734b0807

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Union
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.SetTheory.Cardinal.Finite
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Isohedral
public import Theorems.Thm_DiscreteTiling_TileSet_preimage_quotientPointOfquotientTilePoint_eq_range

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
theorem _root_.solution {t : TileSet ps ιₜ} (x : X)
    (h : t.FiniteDistinctIntersectionsOn {x}) :
    (t.quotientPointOfquotientTilePoint ⁻¹' {⟦x⟧}).Finite := by
  have hf := (h x (Set.mem_singleton _)).to_subtype
  rw [Set.coe_ofPred] at hf
  rw [preimage_quotientPointOfquotientTilePoint_eq_range]
  exact Set.finite_range _
end DiscreteTiling.TileSet
