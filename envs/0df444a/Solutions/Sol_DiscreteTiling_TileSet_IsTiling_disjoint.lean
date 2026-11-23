-- Prove2me | solution 1 for DiscreteTiling.TileSet.IsTiling.disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T05:59:22.941148+00:00
-- url     : https://prove2.me/submissions/abbad08e-8c7d-461e-8493-f95ceda977b4

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Union
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Tiling

set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open DiscreteTiling
open Function
open scoped Pointwise
variable {G X ιₚ : Type*} [Group G] [MulAction G X]
variable {ps : Protoset G X ιₚ} {ιₜ : Type*}
open DiscreteTiling.TileSet
namespace DiscreteTiling.TileSet
namespace IsTiling
theorem _root_.solution {t : TileSet ps ιₜ} (h : t.IsTiling) : t.Disjoint :=
  And.left h
end IsTiling
end DiscreteTiling.TileSet
