-- Prove2me | solution 1 for BooleanIsoperimetry.lowerSatDownFixed_descent_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:43:51.843533+00:00
-- url     : https://prove2.me/submissions/3d5da242-22f1-4a2d-9e4b-8aea421422ba

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
public import Theorems.Thm_BooleanIsoperimetry_paperLevelBlockMove_card
public import Theorems.Thm_BooleanIsoperimetry_paperLevelBlockMove_neighborhood_card_le
public import Theorems.Thm_BooleanIsoperimetry_paperLevelBlockMove_potential_lt
public import Theorems.Thm_BooleanIsoperimetry_not_lowerLevelSaturated_exists_paperLevelBlock
public import Theorems.Thm_BooleanIsoperimetry_coordinateDown_card_eq
public import Theorems.Thm_BooleanIsoperimetry_coordinateDown_neighborhood_card_le
public import Theorems.Thm_BooleanIsoperimetry_coordinateDown_potential_lt_of_ne
public import Theorems.Thm_BooleanIsoperimetry_coordinateDown_spec


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} (A : Finset (Cube N))
    (h : ¬ (IsCoordinateDownFixed A ∧ IsLowerLevelSaturated A)) :
    ∃ A' : Finset (Cube N), A'.card = A.card ∧
      (neighborhood 1 A').card ≤ (neighborhood 1 A).card ∧
      compressionPotential A' < compressionPotential A := by
  by_cases hdf : IsCoordinateDownFixed A
  · have hl : ¬ IsLowerLevelSaturated A := fun hlsat => h ⟨hdf, hlsat⟩
    obtain ⟨A', U, V, hmove⟩ := not_lowerLevelSaturated_exists_paperLevelBlock A hdf hl
    exact ⟨A', paperLevelBlockMove_card hmove,
      paperLevelBlockMove_neighborhood_card_le hmove, paperLevelBlockMove_potential_lt hmove⟩
  · unfold IsCoordinateDownFixed at hdf
    push Not at hdf
    obtain ⟨i, hi⟩ := hdf
    have hne : coordinateDown i A ≠ A := by
      intro heq
      have hspec := coordinateDown_spec i A
      rw [heq] at hspec
      exact hi hspec
    exact ⟨coordinateDown i A, coordinateDown_card_eq (coordinateDown_spec i A),
      coordinateDown_neighborhood_card_le (coordinateDown_spec i A),
      coordinateDown_potential_lt_of_ne i A hne⟩
end BooleanIsoperimetry
