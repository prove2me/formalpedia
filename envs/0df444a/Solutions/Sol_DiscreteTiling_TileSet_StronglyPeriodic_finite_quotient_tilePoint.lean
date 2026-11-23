-- Prove2me | solution 1 for DiscreteTiling.TileSet.StronglyPeriodic.finite_quotient_tilePoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:17:23.173891+00:00
-- url     : https://prove2.me/submissions/5a4f9d05-2c97-4cd0-bea5-e82dcc2593e6

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Tiling
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Isohedral
public import Mathlib.Algebra.Order.Group.Basic
public import Mathlib.LinearAlgebra.FreeModule.Int
public import Mathlib.GroupTheory.OrderOfElement
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Periodic
public import Theorems.Thm_DiscreteTiling_TileSet_stronglyPeriodic_iff
public import Theorems.Thm_DiscreteTiling_TileSet_DisjointOn_finiteDistinctIntersectionsOn
public import Theorems.Thm_DiscreteTiling_TileSet_FiniteDistinctIntersections_finiteDistinctIntersectionsOn
public import Theorems.Thm_DiscreteTiling_TileSet_FiniteIntersectionsOn_finiteDistinctIntersectionsOn
public import Theorems.Thm_DiscreteTiling_TileSet_finite_preimage_quotientPointOfquotientTilePoint


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
namespace StronglyPeriodic
theorem _root_.solution {t : TileSet ps ιₜ} (h : t.StronglyPeriodic)
    (hf : t.FiniteDistinctIntersections) :
    Finite (MulAction.orbitRel.Quotient t.symmetryGroup
      {x : Prod (t : Set (PlacedTile ps)) X // x.2 ∈ (x.1 : PlacedTile ps)}) := by
  rw [← Set.finite_univ_iff, ← Set.preimage_univ (f := t.quotientPointOfquotientTilePoint),
    ← Set.biUnion_preimage_singleton]
  rw [stronglyPeriodic_iff] at h
  refine Finite.Set.finite_biUnion _ _ fun x _ ↦ ?_
  induction x using Quotient.inductionOn' with
  | h x =>
    rw [@Quotient.mk''_eq_mk]
    exact finite_preimage_quotientPointOfquotientTilePoint x
      (FiniteDistinctIntersections.finiteDistinctIntersectionsOn {x} hf)
end StronglyPeriodic
end DiscreteTiling.TileSet
