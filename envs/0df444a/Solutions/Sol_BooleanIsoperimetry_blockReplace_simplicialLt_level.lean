-- Prove2me | solution 1 for BooleanIsoperimetry.blockReplace_simplicialLt_level
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:35:01.554908+00:00
-- url     : https://prove2.me/submissions/f33ccbc6-f748-4bba-918e-1321ba42f8de

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
public import Theorems.Thm_BooleanIsoperimetry_blockReplace_card

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N} {U V S : Cube N}
    (hUS : U ⊆ S) (hVS : Disjoint V S) (hcard : V.card < U.card) :
    simplicialLt (blockReplace U V S) S := by
  have hcle : U.card ≤ S.card := Finset.card_le_card hUS
  have hbc : (blockReplace U V S).card < S.card := by
    rw [blockReplace_card hUS hVS]; omega
  refine ⟨Or.inl hbc, ?_⟩
  rintro (h | ⟨h, _⟩) <;> omega
end BooleanIsoperimetry
