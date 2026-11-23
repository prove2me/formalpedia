-- Prove2me | solution 1 for DiscreteTiling.Protoset.isohedralNumber_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:17:15.110051+00:00
-- url     : https://prove2.me/submissions/f2c476e1-b6cf-4798-ae18-b34c464040c0

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Union
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.SetTheory.Cardinal.Finite
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Isohedral
public import Theorems.Thm_DiscreteTiling_TileSet_isohedralNumber_ne_zero_iff
public import Theorems.Thm_DiscreteTiling_TileSet_isohedralNumber_eq_one_iff
public import Theorems.Thm_DiscreteTiling_TileSet_quotientPlacedTileOfquotientTilePoint_apply_mk
public import Theorems.Thm_DiscreteTiling_TileSet_quotientPointOfquotientTilePoint_apply_mk
public import Theorems.Thm_DiscreteTiling_Protoset_isohedralNumber_ne_zero_iff
public import Theorems.Thm_DiscreteTiling_TileSetFunction_toVarTileSetFunction_apply
public import Theorems.Thm_DiscreteTiling_TileSetFunction_toVarTileSetFunction_const
public import Theorems.Thm_DiscreteTiling_TileSetFunction_toVarTileSetFunction_toTileSetFunction
public import Theorems.Thm_DiscreteTiling_TileSet_coeSet_sigma
public import Theorems.Thm_DiscreteTiling_TileSet_coeSet_sum
public import Theorems.Thm_DiscreteTiling_TileSet_coe_sigma
public import Theorems.Thm_DiscreteTiling_TileSet_coe_sum
public import Theorems.Thm_DiscreteTiling_TileSet_finiteDistinctIntersectionsOn_empty
public import Theorems.Thm_DiscreteTiling_TileSet_finiteDistinctIntersectionsOn_of_subsingleton
public import Theorems.Thm_DiscreteTiling_TileSet_finiteDistinctIntersectionsOn_univ_iff
public import Theorems.Thm_DiscreteTiling_TileSet_mem_sum
public import Theorems.Thm_DiscreteTiling_TileSet_smul_prod_one
public import Theorems.Thm_DiscreteTiling_TileSet_smul_prod_refl
public import Theorems.Thm_DiscreteTiling_TileSet_symmetryGroup_of_isEmpty
public import Theorems.Thm_DiscreteTiling_TileSet_symmetryGroup_reindex
public import Theorems.Thm_DiscreteTiling_TileSet_symmetryGroup_reindex_of_bijective
public import Theorems.Thm_DiscreteTiling_TileSet_unionEqUniv_reindex_iff_of_surjective
attribute [local simp] DiscreteTiling.TileSet.coeSet_sigma
attribute [local simp] DiscreteTiling.TileSet.coeSet_sum
attribute [local simp] DiscreteTiling.TileSet.coe_sigma
attribute [local simp] DiscreteTiling.TileSet.coe_sum
attribute [local simp] DiscreteTiling.TileSet.finiteDistinctIntersectionsOn_empty
attribute [local simp] DiscreteTiling.TileSet.finiteDistinctIntersectionsOn_of_subsingleton
attribute [local simp] DiscreteTiling.TileSet.finiteDistinctIntersectionsOn_univ_iff
attribute [local simp] DiscreteTiling.TileSet.mem_sum
attribute [local simp] DiscreteTiling.TileSet.smul_prod_one
attribute [local simp] DiscreteTiling.TileSet.smul_prod_refl
attribute [local simp] DiscreteTiling.TileSet.symmetryGroup_of_isEmpty
attribute [local simp] DiscreteTiling.TileSet.symmetryGroup_reindex
attribute [local simp] DiscreteTiling.TileSet.symmetryGroup_reindex_of_bijective
attribute [local simp] DiscreteTiling.TileSet.unionEqUniv_reindex_iff_of_surjective
attribute [local simp] DiscreteTiling.TileSetFunction.toVarTileSetFunction_apply
attribute [local simp] DiscreteTiling.TileSetFunction.toVarTileSetFunction_const
attribute [local simp] DiscreteTiling.TileSetFunction.toVarTileSetFunction_toTileSetFunction


attribute [local simp] DiscreteTiling.TileSet.quotientPlacedTileOfquotientTilePoint_apply_mk
attribute [local simp] DiscreteTiling.TileSet.quotientPointOfquotientTilePoint_apply_mk

set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open DiscreteTiling
open Function
open scoped Cardinal Pointwise
variable {G X ιₚ ιₜ : Type*} [Group G] [MulAction G X] {ps : Protoset G X ιₚ}
open DiscreteTiling.Protoset
variable {H : Subgroup G}
namespace DiscreteTiling.Protoset
theorem _root_.solution {p : TileSetFunction ps Prop H} :
    isohedralNumber ιₜ p = 1 ↔ Nonempty ιₜ ∧ ∃ t : TileSet ps ιₜ, p t
      ∧ MulAction.IsPretransitive t.symmetryGroup (t : Set (PlacedTile ps)) := by
  rw [isohedralNumber, iInf]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases Set.eq_empty_or_nonempty (Set.range fun (t : {x : TileSet ps ιₜ // p x}) ↦
      TileSet.isohedralNumber (t : TileSet ps ιₜ)) with he | hn
    · simp [he] at h
    · have h' := csInf_mem hn
      simp only [h, Set.mem_range, Subtype.exists,
        TileSet.isohedralNumber_eq_one_iff] at h'
      rcases h' with ⟨t, hp, hni, hm⟩
      exact ⟨hni, t, hp, hm⟩
  · rcases h with ⟨hn, t, hp, ht⟩
    have hi := TileSet.isohedralNumber_eq_one_iff.2 ⟨hn, ht⟩
    refine IsLeast.csInf_eq ⟨?_, ?_⟩
    · change TileSet.isohedralNumber
        ((⟨t, hp⟩ : {x : TileSet ps ιₜ // p x}) : TileSet ps ιₜ) = 1 at hi
      rw [← hi]
      exact Set.mem_range_self _
    · intro c
      rw [Set.mem_range, Cardinal.one_le_iff_ne_zero]
      rintro ⟨t', rfl⟩
      rwa [TileSet.isohedralNumber_ne_zero_iff]
end DiscreteTiling.Protoset
