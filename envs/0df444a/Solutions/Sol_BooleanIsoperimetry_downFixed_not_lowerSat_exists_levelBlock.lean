-- Prove2me | solution 1 for BooleanIsoperimetry.downFixed_not_lowerSat_exists_levelBlock
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:40:16.052799+00:00
-- url     : https://prove2.me/submissions/0ec0e492-7641-4f0d-a8c9-dca122a09a2b

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
public import Theorems.Thm_BooleanIsoperimetry_blockReplace_sdiff_sdiff_eq_right
public import Theorems.Thm_BooleanIsoperimetry_sdiff_card_lt_sdiff_card_of_card_lt
public import Theorems.Thm_BooleanIsoperimetry_downFixed_not_lowerSat_exists_admissibleBlock

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} {A : Finset (Cube N)}
    (hdown : IsCoordinateDownFixed A) (h : ¬ IsLowerLevelSaturated A) :
    ∃ U V, IsPaperLevelBlockMove A (familyUp U V A) U V := by
  obtain ⟨T, S, hT, hS, hcard, hprimal, hdual⟩ :=
    downFixed_not_lowerSat_exists_admissibleBlock hdown h
  use S \ T, T \ S
  unfold IsPaperLevelBlockMove
  refine ⟨rfl, ?_, disjoint_sdiff_sdiff, sdiff_card_lt_sdiff_card_of_card_lt hcard, hprimal, hdual⟩
  intro heq
  have hblock : blockReplace (S \ T) (T \ S) S = T := blockReplace_sdiff_sdiff_eq_right S T
  have hT_in : T ∈ familyUp (S \ T) (T \ S) A := by
    unfold familyUp familyUpMap
    rw [Finset.mem_image]
    use S
    refine ⟨hS, ?_⟩
    split_ifs with h_if
    · exact hblock
    · push Not at h_if
      have h_subset : S \ T ⊆ S := sdiff_subset
      have h_disj : Disjoint (T \ S) S := Disjoint.symm disjoint_sdiff
      have h_not_in : blockReplace (S \ T) (T \ S) S ∉ A := by
        rw [hblock]
        exact hT
      exfalso
      exact h_not_in (h_if h_subset h_disj)
  rw [heq] at hT_in
  exact hT hT_in
end BooleanIsoperimetry
