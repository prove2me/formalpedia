-- Prove2me | solution 1 for DiscreteTiling.TileSet.finiteLocalComplexity_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:17:11.260075+00:00
-- url     : https://prove2.me/submissions/72daa562-440c-4678-9292-0cdb93aeeb6a

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
theorem _root_.solution {H : Subgroup G} {t : TileSet ps ιₜ} :
    t.FiniteLocalComplexity H ↔
      ((fun x ↦ Quotient.mk (MulAction.orbitRel H (Set X × TileSetCard ps))
        (x, (t.patch x).card)) '' (Set.range Singleton.singleton)).Finite :=
  Iff.rfl
end DiscreteTiling.TileSet
