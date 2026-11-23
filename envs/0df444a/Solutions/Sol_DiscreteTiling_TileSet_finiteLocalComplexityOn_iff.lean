-- Prove2me | solution 1 for DiscreteTiling.TileSet.finiteLocalComplexityOn_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:14:07.742381+00:00
-- url     : https://prove2.me/submissions/6d6778be-d4b4-44d7-bc89-b0189910b2b9

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Basic
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Patch
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSetCard
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_FiniteLocalComplexity

set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open DiscreteTiling
open Function
open scoped Pointwise
variable {G X ιₚ : Type*} [Group G] [MulAction G X]
variable {ps : Protoset G X ιₚ} {ιₜ ιₜ' : Type*}
open DiscreteTiling.TileSet
namespace DiscreteTiling.TileSet
theorem _root_.solution {H : Subgroup G} {s : Set (Set X)} {t : TileSet ps ιₜ} :
    t.FiniteLocalComplexityOn H s ↔
      ((fun x ↦ Quotient.mk (MulAction.orbitRel H (Set X × TileSetCard ps))
        (x, (t.patch x).card)) '' s).Finite :=
  Iff.rfl
end DiscreteTiling.TileSet
