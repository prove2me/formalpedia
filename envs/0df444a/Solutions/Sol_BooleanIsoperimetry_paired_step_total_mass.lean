-- Prove2me | solution 1 for BooleanIsoperimetry.paired_step_total_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:43:19.664042+00:00
-- url     : https://prove2.me/submissions/308c90c7-eb11-4cee-b93d-e0a0fd431a72

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

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} {A B A' B' : Finset (Cube N)}
    (step : IsPairedCompressionStep A B A' B') :
    A'.card + B'.card = A.card + B.card := by
  cases step with
  | coord i A' B' hA hB =>
      rw [hA.1, hB.1]
  | cascade A' B' hTerm hTarget hTotal hCost hProgress =>
      exact hTotal
end BooleanIsoperimetry
