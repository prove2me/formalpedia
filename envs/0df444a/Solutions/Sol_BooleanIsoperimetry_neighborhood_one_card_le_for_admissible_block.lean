-- Prove2me | solution 1 for BooleanIsoperimetry.neighborhood_one_card_le_for_admissible_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:40:06.34427+00:00
-- url     : https://prove2.me/submissions/fa29a6a0-9bfb-46de-954b-15ae630fe06e

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
public import Theorems.Thm_BooleanIsoperimetry_neighborhood_one_subset_familyUp_neighborhood_of_admissible

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ}
    {A : Finset (Cube N)} {U V : Cube N}
    (hd : Disjoint U V)
    (hadm : IsUVAdmissibleForFamily A U V)
    (hadm' : IsUVAdmissibleForFamily (Aᶜˢ) V U) :
    (neighborhood 1 (familyUp U V A)).card ≤ (neighborhood 1 A).card := by
  have h_sub := neighborhood_one_subset_familyUp_neighborhood_of_admissible hd hadm hadm'
  have h_le := Finset.card_le_card h_sub
  rw [familyUp_card U V (neighborhood 1 A)] at h_le
  exact h_le
end BooleanIsoperimetry
