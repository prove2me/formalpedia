-- Prove2me | solution 1 for BooleanIsoperimetry.paperLevelBlockMove_neighborhood_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:41:24.807035+00:00
-- url     : https://prove2.me/submissions/330227be-e3c1-47dc-8dc4-d94a114117b4

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
public import Theorems.Thm_BooleanIsoperimetry_neighborhood_one_card_le_for_admissible_block

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} {A A' : Finset (Cube N)} {U V : Cube N}
    (h : IsPaperLevelBlockMove A A' U V) : (neighborhood 1 A').card ≤ (neighborhood 1 A).card := by
  have hd : Disjoint U V := h.2.2.1
  have hadm : IsUVAdmissibleForFamily A U V := h.2.2.2.2.1
  have hadm' : IsUVAdmissibleForFamily (Aᶜˢ) V U := h.2.2.2.2.2
  rw [h.1]
  exact neighborhood_one_card_le_for_admissible_block hd hadm hadm'
end BooleanIsoperimetry
