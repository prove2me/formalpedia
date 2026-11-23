-- Prove2me | solution 1 for DiscreteTiling.TileSet.StronglyPeriodic.isohedralNumber_lt_aleph0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:18:10.65291+00:00
-- url     : https://prove2.me/submissions/fa468f7e-f485-4dfc-a7bf-631f52d6b25e

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Tiling
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Isohedral
public import Mathlib.Algebra.Order.Group.Basic
public import Mathlib.LinearAlgebra.FreeModule.Int
public import Mathlib.GroupTheory.OrderOfElement
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Periodic
public import Theorems.Thm_DiscreteTiling_TileSet_StronglyPeriodic_finite_quotient_tilePoint
public import Theorems.Thm_DiscreteTiling_TileSet_isohedralNumber_lt_aleph0_of_finite_quotient_tilePoint


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
    (hf : t.FiniteDistinctIntersections) (hn : ∀ i, (t i : Set X).Nonempty) :
    t.isohedralNumber < ℵ₀ :=
  isohedralNumber_lt_aleph0_of_finite_quotient_tilePoint
    (StronglyPeriodic.finite_quotient_tilePoint h hf) hn
end StronglyPeriodic
end DiscreteTiling.TileSet
