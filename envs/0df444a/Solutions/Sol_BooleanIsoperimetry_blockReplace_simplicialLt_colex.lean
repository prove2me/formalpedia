-- Prove2me | solution 1 for BooleanIsoperimetry.blockReplace_simplicialLt_colex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:36:05.404877+00:00
-- url     : https://prove2.me/submissions/f6a07136-7b46-47c9-90f0-faafb2efadcc

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
public import Theorems.Thm_BooleanIsoperimetry_cubeToNat_le_of_subset
public import Theorems.Thm_BooleanIsoperimetry_blockReplace_card
public import Theorems.Thm_BooleanIsoperimetry_cubeToNat_blockReplace

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N} {U V S : Cube N}
    (hUS : U ⊆ S) (hVS : Disjoint V S) (hcard : U.card = V.card)
    (hVU : simplicialLt V U) :
    simplicialLt (blockReplace U V S) S := by
  have hbc : (blockReplace U V S).card = S.card := by
    rw [blockReplace_card hUS hVS]
    have : U.card ≤ S.card := Finset.card_le_card hUS
    omega
  have hUV_nat : cubeToNat U < cubeToNat V := by
    obtain ⟨hle, hnle⟩ := hVU
    unfold simplicialLe at hle hnle
    rcases hle with h | ⟨_, h⟩
    · omega
    · rcases lt_or_eq_of_le h with h2 | h2
      · exact h2
      · exfalso; apply hnle; right; exact ⟨hcard, le_of_eq h2.symm⟩
  have hUleS : cubeToNat U ≤ cubeToNat S := cubeToNat_le_of_subset hUS
  have hbr_nat : cubeToNat S < cubeToNat (blockReplace U V S) := by
    rw [cubeToNat_blockReplace hUS hVS]; omega
  refine ⟨Or.inr ⟨hbc, le_of_lt hbr_nat⟩, ?_⟩
  rintro (h | ⟨_, h⟩) <;> omega
end BooleanIsoperimetry
