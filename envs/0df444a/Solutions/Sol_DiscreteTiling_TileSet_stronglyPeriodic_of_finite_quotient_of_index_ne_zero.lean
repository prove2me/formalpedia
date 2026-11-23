-- Prove2me | solution 1 for DiscreteTiling.TileSet.stronglyPeriodic_of_finite_quotient_of_index_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:10:26.812336+00:00
-- url     : https://prove2.me/submissions/27d97981-bd59-43a3-874e-9718fe52f43b

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Tiling
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Isohedral
public import Mathlib.Algebra.Order.Group.Basic
public import Mathlib.LinearAlgebra.FreeModule.Int
public import Mathlib.GroupTheory.OrderOfElement
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Periodic

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
    [Finite <| MulAction.orbitRel.Quotient G X] (hi : t.symmetryGroup.index ≠ 0) :
    t.StronglyPeriodic :=
  Subgroup.finite_quotient_of_finite_quotient_of_index_ne_zero hi
end DiscreteTiling.TileSet
