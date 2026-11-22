-- Prove2me | solution 1 for BooleanIsoperimetry.cubeToNat_sdiff_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:25:13.453775+00:00
-- url     : https://prove2.me/submissions/f7fb8a90-b0a2-4fd2-b990-0d7f37a35f15

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

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N} {U S : Cube N} (h : U ⊆ S) :
    cubeToNat (S \ U) + cubeToNat U = cubeToNat S := by
  rw [← cubeToNat_union_disjoint (Finset.sdiff_disjoint), Finset.sdiff_union_of_subset h]
end BooleanIsoperimetry
