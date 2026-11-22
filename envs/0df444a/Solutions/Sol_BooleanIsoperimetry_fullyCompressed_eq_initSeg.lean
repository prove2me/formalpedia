-- Prove2me | solution 1 for BooleanIsoperimetry.fullyCompressed_eq_initSeg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:34:28.138862+00:00
-- url     : https://prove2.me/submissions/195aa605-f360-4756-bf01-e3455755350b

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
public import Theorems.Thm_BooleanIsoperimetry_downwardClosed_eq_initSeg
public import Theorems.Thm_BooleanIsoperimetry_lowerLevelSaturated_colexFixed_is_downClosed


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} (A : Finset (Cube N))
    (h : IsFullyCompressed A) : A = simplicialInitSeg N A.card :=
  downwardClosed_eq_initSeg
    (lowerLevelSaturated_colexFixed_is_downClosed A h.1 h.2)
end BooleanIsoperimetry
