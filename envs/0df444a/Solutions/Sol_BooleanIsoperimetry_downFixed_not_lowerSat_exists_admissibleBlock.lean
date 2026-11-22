-- Prove2me | solution 1 for BooleanIsoperimetry.downFixed_not_lowerSat_exists_admissibleBlock
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:39:16.566032+00:00
-- url     : https://prove2.me/submissions/cd237433-e17f-49ea-a36b-280f88876763

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
public import Theorems.Thm_BooleanIsoperimetry_not_lowerSat_exists_minDelta_pair
public import Theorems.Thm_BooleanIsoperimetry_minDelta_pair_admissible

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
    ∃ (T S : Cube N), T ∉ A ∧ S ∈ A ∧ T.card < S.card ∧
    (∀ x ∈ T \ S, ∃ y ∈ S \ T, familyUp ((S \ T).erase y) ((T \ S).erase x) A = A) ∧
    (∀ x ∈ S \ T, ∃ y ∈ T \ S, familyUp ((T \ S).erase y) ((S \ T).erase x) Aᶜˢ = Aᶜˢ) := by
  obtain ⟨T, S, hT, hS, hcard, hmin⟩ :=
    not_lowerSat_exists_minDelta_pair h
  obtain ⟨hprimal, hdual⟩ :=
    minDelta_pair_admissible hdown hT hS hcard hmin
  exact ⟨T, S, hT, hS, hcard, hprimal, hdual⟩
end BooleanIsoperimetry
