-- Prove2me | solution 1 for BooleanIsoperimetry.paperColexShiftMove_potential_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:37:34.102111+00:00
-- url     : https://prove2.me/submissions/39868e0d-2230-46b2-b31a-288942c104b3

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
public import Theorems.Thm_BooleanIsoperimetry_swap_potential_lt
public import Theorems.Thm_BooleanIsoperimetry_paperColexBlockMove_potential_lt

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} {A A' : Finset (Cube N)}
    (h : IsPaperColexShiftMove A A') : compressionPotential A' < compressionPotential A := by
  rcases h with h_colex | ⟨i, j, h_block⟩
  · rcases h_colex with ⟨_hcard, x, y, hx, hy, _hxycard, hlt, heq⟩
    exact swap_potential_lt hx hy hlt heq
  · exact paperColexBlockMove_potential_lt h_block
end BooleanIsoperimetry
