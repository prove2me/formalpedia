-- Prove2me | solution 1 for DiscreteTiling.TileSet.weaklyPeriodic_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:23:26.639811+00:00
-- url     : https://prove2.me/submissions/fd230e19-12f4-40ac-8dbb-b819ec828b9f

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
theorem _root_.solution {t : TileSet ps ιₜ} {m n : ℕ} (h : t.WeaklyPeriodic n) (hle : m ≤ n) :
    t.WeaklyPeriodic m := by
  rcases h with ⟨f, hf⟩
  exact ⟨f.comp (ExtendByOne.hom (Multiplicative ℤ) (Fin.castLE hle)),
         hf.comp (extend_injective (Fin.strictMono_castLE hle).injective _)⟩
end DiscreteTiling.TileSet
