-- Prove2me | solution 1 for DiscreteTiling.TileSet.weaklyPeriodic_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:12:09.562802+00:00
-- url     : https://prove2.me/submissions/3f9cf8e7-73df-4a71-9d6a-9d9ef96154d4

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
theorem _root_.solution {n : ℕ} {t : TileSet ps ιₜ} :
    t.WeaklyPeriodic n ↔ ∃ f : (Fin n → Multiplicative ℤ) →* t.symmetryGroup, Injective f :=
  Iff.rfl
end DiscreteTiling.TileSet
