-- Prove2me | solution 1 for BooleanIsoperimetry.paperLevelBlockMove_potential_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:36:08.203459+00:00
-- url     : https://prove2.me/submissions/fb69f227-ff79-41a4-b2e5-df5e3bf9b1c3

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
public import Theorems.Thm_BooleanIsoperimetry_blockReplace_simplicialLt_level
public import Theorems.Thm_BooleanIsoperimetry_familyUp_potential_lt_of_blockLt

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} {A A' : Finset (Cube N)} {U V : Cube N}
    (h : IsPaperLevelBlockMove A A' U V) : compressionPotential A' < compressionPotential A := by
  obtain ⟨heq, hne, _hd, hcard, _, _⟩ := h
  rw [heq]
  refine familyUp_potential_lt_of_blockLt (heq ▸ hne) ?_
  intro S hUS hVS
  exact blockReplace_simplicialLt_level hUS hVS hcard
end BooleanIsoperimetry
