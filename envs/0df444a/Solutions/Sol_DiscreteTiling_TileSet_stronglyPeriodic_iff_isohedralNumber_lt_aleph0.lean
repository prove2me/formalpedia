-- Prove2me | solution 1 for DiscreteTiling.TileSet.stronglyPeriodic_iff_isohedralNumber_lt_aleph0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:23:15.885738+00:00
-- url     : https://prove2.me/submissions/061f881c-4dce-4c7c-a016-eec4c4193bbf

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Tiling
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Isohedral
public import Mathlib.Algebra.Order.Group.Basic
public import Mathlib.LinearAlgebra.FreeModule.Int
public import Mathlib.GroupTheory.OrderOfElement
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Periodic
public import Theorems.Thm_DiscreteTiling_TileSet_stronglyPeriodic_of_isohedralNumber_lt_aleph0
public import Theorems.Thm_DiscreteTiling_TileSet_StronglyPeriodic_isohedralNumber_lt_aleph0
public import Theorems.Thm_DiscreteTiling_TileSet_Disjoint_finiteDistinctIntersections
public import Theorems.Thm_DiscreteTiling_TileSet_IsTilingOf_finiteDistinctIntersections
public import Theorems.Thm_DiscreteTiling_TileSet_IsTiling_finiteDistinctIntersections
public import Theorems.Thm_DiscreteTiling_TileSet_IsTiling_unionEqUniv


set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open DiscreteTiling
open Function
open scoped Cardinal Nat Pointwise
variable {G X ιₚ ιₜ : Type*} [Group G] [MulAction G X] {ps : Protoset G X ιₚ}
open DiscreteTiling.TileSet
namespace DiscreteTiling.TileSet
theorem _root_.solution {t : TileSet ps ιₜ} (ht : t.IsTiling)
    (hf : ∀ i, (t i : Set X).Finite) (hn : ∀ i, (t i : Set X).Nonempty) :
    t.StronglyPeriodic ↔ t.isohedralNumber < ℵ₀ :=
  ⟨fun h ↦ StronglyPeriodic.isohedralNumber_lt_aleph0 h
    (IsTiling.finiteDistinctIntersections ht) hn,
   fun h ↦ stronglyPeriodic_of_isohedralNumber_lt_aleph0 h hf (IsTiling.unionEqUniv ht)⟩
end DiscreteTiling.TileSet
