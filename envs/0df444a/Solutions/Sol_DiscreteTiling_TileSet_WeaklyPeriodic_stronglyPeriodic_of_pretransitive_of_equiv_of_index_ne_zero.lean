-- Prove2me | solution 1 for DiscreteTiling.TileSet.WeaklyPeriodic.stronglyPeriodic_of_pretransitive_of_equiv_of_index_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:23:33.280801+00:00
-- url     : https://prove2.me/submissions/860895f2-53c3-41aa-9b00-b49dd2471c78

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Tiling
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Isohedral
public import Mathlib.Algebra.Order.Group.Basic
public import Mathlib.LinearAlgebra.FreeModule.Int
public import Mathlib.GroupTheory.OrderOfElement
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Periodic
public import Theorems.Thm_DiscreteTiling_TileSet_WeaklyPeriodic_stronglyPeriodic_of_finite_quotient_of_equiv_of_index_ne_zero

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
namespace WeaklyPeriodic
theorem _root_.solution {n : ℕ}
    {t : TileSet ps ιₜ} (h : t.WeaklyPeriodic n) [MulAction.IsPretransitive G X] {H : Subgroup G}
    (e : H ≃* (Fin n → Multiplicative ℤ)) (hi : H.index ≠ 0) : t.StronglyPeriodic := by
  have : Subsingleton <| MulAction.orbitRel.Quotient G X :=
    (MulAction.pretransitive_iff_subsingleton_quotient _ _).1 inferInstance
  exact WeaklyPeriodic.stronglyPeriodic_of_finite_quotient_of_equiv_of_index_ne_zero h e hi
end WeaklyPeriodic
end DiscreteTiling.TileSet
