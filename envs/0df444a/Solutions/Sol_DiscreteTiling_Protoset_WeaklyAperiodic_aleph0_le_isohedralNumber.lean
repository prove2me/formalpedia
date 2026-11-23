-- Prove2me | solution 1 for DiscreteTiling.Protoset.WeaklyAperiodic.aleph0_le_isohedralNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:19:09.562384+00:00
-- url     : https://prove2.me/submissions/b8bb170e-6b4e-48de-bd4e-403cdaa153d3

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Tiling
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Isohedral
public import Mathlib.Algebra.Order.Group.Basic
public import Mathlib.LinearAlgebra.FreeModule.Int
public import Mathlib.GroupTheory.OrderOfElement
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Periodic
public import Theorems.Thm_DiscreteTiling_TileSet_stronglyPeriodic_of_isohedralNumber_lt_aleph0
public import Theorems.Thm_DiscreteTiling_Protoset_le_isohedralNumber_iff
public import Theorems.Thm_DiscreteTiling_TileSet_finite_apply_of_forall_finite


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
namespace WeaklyAperiodic
theorem _root_.solution {p : TileSetFunction ps Prop H}
    (h : ps.WeaklyAperiodic ιₜ p) (hf : ∀ i, (ps i : Set X).Finite)
    (hu : ∀ t : TileSet ps ιₜ, p t → t.UnionEqUniv) : ℵ₀ ≤ ps.isohedralNumber ιₜ p := by
  rw [le_isohedralNumber_iff Cardinal.aleph0_ne_zero]
  rcases h with ⟨he, hnp⟩
  refine ⟨he, fun t hpt ↦ ?_⟩
  by_contra hi
  rw [not_le] at hi
  refine hnp t hpt (TileSet.stronglyPeriodic_of_isohedralNumber_lt_aleph0 hi
    (t.finite_apply_of_forall_finite hf) (hu t hpt))
end WeaklyAperiodic
end DiscreteTiling.Protoset
