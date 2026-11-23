-- Prove2me | solution 1 for DiscreteTiling.Protoset.weaklyAperiodic_iff_aleph0_le_isohedralNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:23:44.216718+00:00
-- url     : https://prove2.me/submissions/1e1e9ae4-e02c-4847-8977-8e1372519a14

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Tiling
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Isohedral
public import Mathlib.Algebra.Order.Group.Basic
public import Mathlib.LinearAlgebra.FreeModule.Int
public import Mathlib.GroupTheory.OrderOfElement
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Periodic
public import Theorems.Thm_DiscreteTiling_Protoset_WeaklyAperiodic_aleph0_le_isohedralNumber
public import Theorems.Thm_DiscreteTiling_Protoset_weaklyAperiodic_of_aleph0_le_isohedralNumber
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
open DiscreteTiling.Protoset
variable {H : Subgroup G}
namespace DiscreteTiling.Protoset
theorem _root_.solution {p : TileSetFunction ps Prop H}
    (ht : ∀ t : TileSet ps ιₜ, p t → t.IsTiling) (hf : ∀ i, (ps i : Set X).Finite)
    (hn : ∀ i, (ps i : Set X).Nonempty) : ps.WeaklyAperiodic ιₜ p ↔ ℵ₀ ≤ ps.isohedralNumber ιₜ p :=
  ⟨fun h ↦ h.aleph0_le_isohedralNumber hf fun t hpt ↦ TileSet.IsTiling.unionEqUniv (ht t hpt),
   fun h ↦ weaklyAperiodic_of_aleph0_le_isohedralNumber h
     (fun t hpt ↦ TileSet.IsTiling.finiteDistinctIntersections (ht t hpt)) hn⟩
end DiscreteTiling.Protoset
