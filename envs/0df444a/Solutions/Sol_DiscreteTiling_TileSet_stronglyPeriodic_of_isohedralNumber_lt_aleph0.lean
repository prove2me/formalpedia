-- Prove2me | solution 1 for DiscreteTiling.TileSet.stronglyPeriodic_of_isohedralNumber_lt_aleph0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:18:09.743717+00:00
-- url     : https://prove2.me/submissions/537f77a3-5fad-45c8-ae9c-e3c80735a4e8

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Tiling
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Isohedral
public import Mathlib.Algebra.Order.Group.Basic
public import Mathlib.LinearAlgebra.FreeModule.Int
public import Mathlib.GroupTheory.OrderOfElement
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Periodic
public import Theorems.Thm_DiscreteTiling_TileSet_stronglyPeriodic_of_finite_quotient_tilePoint
public import Theorems.Thm_DiscreteTiling_TileSet_finite_quotient_tilePoint_of_isohedralNumber_lt_aleph0


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
theorem _root_.solution {t : TileSet ps ιₜ} (h : t.isohedralNumber < ℵ₀)
    (hf : ∀ i, (t i : Set X).Finite) (hu : t.UnionEqUniv) : t.StronglyPeriodic :=
  stronglyPeriodic_of_finite_quotient_tilePoint
    (finite_quotient_tilePoint_of_isohedralNumber_lt_aleph0 h hf) hu
end DiscreteTiling.TileSet
