-- Prove2me | solution 1 for DiscreteTiling.TileSet.symmetryGroup_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T05:54:21.07596+00:00
-- url     : https://prove2.me/submissions/2704746f-ee56-472a-b4b4-c39bdd238b57

module
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Combinatorics.Tiling.Tile
public import Mathlib.GroupTheory.GroupAction.Basic
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSet
public import Theorems.Thm_DiscreteTiling_TileSet_smul_prod_one
public import Theorems.Thm_DiscreteTiling_TileSet_smul_prod_refl
public import Theorems.Thm_DiscreteTiling_TileSet_symmetryGroup_of_isEmpty
public import Theorems.Thm_DiscreteTiling_TileSet_symmetryGroup_reindex
public import Theorems.Thm_DiscreteTiling_TileSet_symmetryGroup_reindex_of_bijective
attribute [local simp] DiscreteTiling.TileSet.smul_prod_one
attribute [local simp] DiscreteTiling.TileSet.smul_prod_refl
attribute [local simp] DiscreteTiling.TileSet.symmetryGroup_of_isEmpty
attribute [local simp] DiscreteTiling.TileSet.symmetryGroup_reindex
attribute [local simp] DiscreteTiling.TileSet.symmetryGroup_reindex_of_bijective

set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open DiscreteTiling
open Function
open scoped Pointwise
variable {G X ιₚ : Type*} [Group G] [MulAction G X]
variable {ps : Protoset G X ιₚ} {ι ιₜ ιₜ' ιₜ'' ιₜ''' E E' F : Type*} {ιₜι ιₜ'ι : ι → Type*}
variable [EquivLike E ιₜ' ιₜ] [EquivLike E' ιₜ'' ιₜ'] [FunLike F ιₜ' ιₜ] [EmbeddingLike F ιₜ' ιₜ]
open DiscreteTiling.TileSet
attribute [coe] tiles
namespace DiscreteTiling.TileSet
theorem _root_.solution (t : TileSet ps ιₜ) (g : G) :
    (g • t).symmetryGroup = (ConjAct.toConjAct g) • t.symmetryGroup := by
  simp_rw [← smul_prod_one, symmetryGroup, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  ext h
  simp only [Subgroup.mem_map, MulAction.mem_stabilizer_iff, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, Prod.inv_mk, inv_one, Prod.exists, Prod.mk_mul_mk, one_mul, mul_one,
    MonoidHom.coe_fst, Prod.mk.injEq, exists_eq_right_right, exists_and_right, exists_eq_right,
    Subgroup.mem_smul_pointwise_iff_exists, ConjAct.smul_def, ConjAct.ofConjAct_toConjAct]
  rw [exists_comm]
  convert Iff.rfl
  rw [exists_and_right]
end DiscreteTiling.TileSet
