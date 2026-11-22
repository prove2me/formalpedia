-- Prove2me | solution 1 for BooleanIsoperimetry.familyUpDown_total
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:43:20.534107+00:00
-- url     : https://prove2.me/submissions/7c78e4cb-4f33-4178-aa24-d4f5aa3148a1

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
public import Theorems.Thm_BooleanIsoperimetry_familyUp_card
public import Theorems.Thm_BooleanIsoperimetry_familyDown_card

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} (U V : Cube N) (𝒜 ℬ : Finset (Cube N)) :
    (familyUp U V 𝒜).card + (familyDown U V ℬ).card = 𝒜.card + ℬ.card := by
  rw [familyUp_card, familyDown_card]
end BooleanIsoperimetry
