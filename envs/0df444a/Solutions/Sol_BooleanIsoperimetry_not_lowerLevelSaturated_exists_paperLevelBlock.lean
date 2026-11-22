-- Prove2me | solution 1 for BooleanIsoperimetry.not_lowerLevelSaturated_exists_paperLevelBlock
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:43:15.509729+00:00
-- url     : https://prove2.me/submissions/70a107b9-b83f-41c6-8d2d-f53c6fbad6d8

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
public import Theorems.Thm_BooleanIsoperimetry_downFixed_not_lowerSat_exists_levelBlock

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution
    {N : ℕ} (A : Finset (Cube N))
    (hdown : IsCoordinateDownFixed A)
    (h : ¬ IsLowerLevelSaturated A) :
    ∃ A' U V, IsPaperLevelBlockMove A A' U V := by
  obtain ⟨U, V, hmove⟩ := downFixed_not_lowerSat_exists_levelBlock hdown h
  exact ⟨familyUp U V A, U, V, hmove⟩
end BooleanIsoperimetry
