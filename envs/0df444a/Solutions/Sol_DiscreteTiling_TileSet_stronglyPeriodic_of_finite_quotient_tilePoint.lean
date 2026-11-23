-- Prove2me | solution 1 for DiscreteTiling.TileSet.stronglyPeriodic_of_finite_quotient_tilePoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:11:47.628619+00:00
-- url     : https://prove2.me/submissions/1f6cda32-2624-4648-beda-7ed09f998c8d

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Tiling
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Isohedral
public import Mathlib.Algebra.Order.Group.Basic
public import Mathlib.LinearAlgebra.FreeModule.Int
public import Mathlib.GroupTheory.OrderOfElement
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Periodic
public import Theorems.Thm_DiscreteTiling_TileSet_stronglyPeriodic_iff
public import Theorems.Thm_DiscreteTiling_TileSet_surjective_quotientPointOfquotientTilePoint


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
theorem _root_.solution {t : TileSet ps ιₜ}
    (hf : Finite (MulAction.orbitRel.Quotient t.symmetryGroup
      {x : Prod (t : Set (PlacedTile ps)) X // x.2 ∈ (x.1 : PlacedTile ps)}))
    (hu : t.UnionEqUniv) : t.StronglyPeriodic := by
  rw [stronglyPeriodic_iff]
  rw [← Set.finite_univ_iff] at hf ⊢
  exact Set.Finite.of_surjOn t.quotientPointOfquotientTilePoint
    (Set.surjOn_univ.2 (surjective_quotientPointOfquotientTilePoint hu)) hf
end DiscreteTiling.TileSet
