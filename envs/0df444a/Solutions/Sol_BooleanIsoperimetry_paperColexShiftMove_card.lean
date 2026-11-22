-- Prove2me | solution 1 for BooleanIsoperimetry.paperColexShiftMove_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:35:23.704936+00:00
-- url     : https://prove2.me/submissions/8e43d77a-4284-4457-aac7-de0c6cd4694d

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
public import Theorems.Thm_BooleanIsoperimetry_paperColexBlockMove_card

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} {A A' : Finset (Cube N)}
    (h : IsPaperColexShiftMove A A') : A'.card = A.card := by
  rcases h with h_colex | ⟨i, j, h_block⟩
  · exact h_colex.1
  · exact paperColexBlockMove_card h_block
end BooleanIsoperimetry
