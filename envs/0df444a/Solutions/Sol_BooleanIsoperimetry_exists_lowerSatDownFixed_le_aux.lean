-- Prove2me | solution 1 for BooleanIsoperimetry.exists_lowerSatDownFixed_le_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:44:50.350637+00:00
-- url     : https://prove2.me/submissions/0c558ba0-6f33-4478-a40a-6b914c8bd7b6

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
public import Theorems.Thm_BooleanIsoperimetry_lowerSatDownFixed_descent_step

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} :
    ∀ n (A : Finset (Cube N)), compressionPotential A = n →
      ∃ A₁ : Finset (Cube N), IsCoordinateDownFixed A₁ ∧ IsLowerLevelSaturated A₁ ∧
        A₁.card = A.card ∧ (neighborhood 1 A₁).card ≤ (neighborhood 1 A).card := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A hA
    by_cases h : IsCoordinateDownFixed A ∧ IsLowerLevelSaturated A
    · exact ⟨A, h.1, h.2, rfl, le_rfl⟩
    · obtain ⟨A', hcard, hnbhd, hpot⟩ := lowerSatDownFixed_descent_step A h
      rw [hA] at hpot
      obtain ⟨A₁, hdf, hls, hc, hn⟩ := ih (compressionPotential A') hpot A' rfl
      exact ⟨A₁, hdf, hls, hc.trans hcard, hn.trans hnbhd⟩
end BooleanIsoperimetry
