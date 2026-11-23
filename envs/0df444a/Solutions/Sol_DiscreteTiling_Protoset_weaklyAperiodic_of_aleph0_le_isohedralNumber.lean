-- Prove2me | solution 1 for DiscreteTiling.Protoset.weaklyAperiodic_of_aleph0_le_isohedralNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:18:57.742794+00:00
-- url     : https://prove2.me/submissions/c6b1b431-010e-4f6c-8ee6-5b486b5016f6

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Tiling
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Isohedral
public import Mathlib.Algebra.Order.Group.Basic
public import Mathlib.LinearAlgebra.FreeModule.Int
public import Mathlib.GroupTheory.OrderOfElement
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Periodic
public import Theorems.Thm_DiscreteTiling_TileSet_StronglyPeriodic_isohedralNumber_lt_aleph0
public import Theorems.Thm_DiscreteTiling_Protoset_le_isohedralNumber_iff
public import Theorems.Thm_DiscreteTiling_TileSet_nonempty_apply_of_forall_nonempty


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
    (h : ℵ₀ ≤ ps.isohedralNumber ιₜ p)
    (hf : ∀ t : TileSet ps ιₜ, p t → t.FiniteDistinctIntersections)
    (hn : ∀ i, (ps i : Set X).Nonempty) : ps.WeaklyAperiodic ιₜ p := by
  rw [le_isohedralNumber_iff Cardinal.aleph0_ne_zero] at h
  rcases h with ⟨he, hnp⟩
  refine ⟨he, fun t hpt hp ↦ ?_⟩
  have hi := hnp t hpt
  revert hi
  rw [← Not, not_le]
  refine TileSet.StronglyPeriodic.isohedralNumber_lt_aleph0 hp (hf t hpt)
    (t.nonempty_apply_of_forall_nonempty hn)
end DiscreteTiling.Protoset
