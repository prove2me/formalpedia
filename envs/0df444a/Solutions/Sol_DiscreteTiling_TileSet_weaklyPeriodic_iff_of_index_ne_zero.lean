-- Prove2me | solution 1 for DiscreteTiling.TileSet.weaklyPeriodic_iff_of_index_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:18:31.809808+00:00
-- url     : https://prove2.me/submissions/200c7335-2c58-4c54-a15e-d7f4cb7b602c

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Tiling
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Isohedral
public import Mathlib.Algebra.Order.Group.Basic
public import Mathlib.LinearAlgebra.FreeModule.Int
public import Mathlib.GroupTheory.OrderOfElement
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Periodic
public import Theorems.Thm_DiscreteTiling_TileSet_weaklyPeriodic_iff_of_relIndex_ne_zero

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
theorem _root_.solution {n : ℕ} {t : TileSet ps ιₜ} {H : Subgroup G}
    (hi : H.index ≠ 0) :
    t.WeaklyPeriodic n ↔
      ∃ f : (Fin n → Multiplicative ℤ) →* (H ⊓ t.symmetryGroup : Subgroup G), Injective f :=
  weaklyPeriodic_iff_of_relIndex_ne_zero (mt Subgroup.index_eq_zero_of_relIndex_eq_zero hi)
end DiscreteTiling.TileSet
