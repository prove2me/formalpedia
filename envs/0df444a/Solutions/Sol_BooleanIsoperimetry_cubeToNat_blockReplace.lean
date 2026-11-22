-- Prove2me | solution 1 for BooleanIsoperimetry.cubeToNat_blockReplace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:35:00.796477+00:00
-- url     : https://prove2.me/submissions/4347b599-1be4-4a8c-9330-5982cb831a3a

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Definitions.Def_LeanPool_BooleanIsoperimetry_LayerWindows
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Combinatorics.SetFamily.Compression.UV
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Compression
public import Theorems.Thm_BooleanIsoperimetry_cubeToNat_union_disjoint
public import Theorems.Thm_BooleanIsoperimetry_cubeToNat_sdiff_add

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N} {U V S : Cube N} (hUS : U ⊆ S) (hVS : Disjoint V S) :
    cubeToNat (blockReplace U V S) = cubeToNat S - cubeToNat U + cubeToNat V := by
  unfold blockReplace
  rw [cubeToNat_union_disjoint (Disjoint.disjoint_sdiff_left (Disjoint.symm hVS))]
  have := cubeToNat_sdiff_add hUS; omega
end BooleanIsoperimetry
