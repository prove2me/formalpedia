-- Prove2me | solution 1 for BooleanIsoperimetry.paperColexShiftMove_isResidualShift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:38:27.812258+00:00
-- url     : https://prove2.me/submissions/cc85f050-0582-4c08-82dc-fc4af7cf99a3

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
public import Theorems.Thm_BooleanIsoperimetry_paperColexShiftMove_card
public import Theorems.Thm_BooleanIsoperimetry_paperColexShiftMove_potential_lt

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} {A A' : Finset (Cube N)}
    (h : IsPaperColexShiftMove A A')
    (hnbhd : (neighborhood 1 A').card ≤ (neighborhood 1 A).card) :
    IsDownFixedResidualShift A A' :=
  ⟨paperColexShiftMove_card h, hnbhd, paperColexShiftMove_potential_lt h⟩
end BooleanIsoperimetry
