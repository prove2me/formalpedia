-- Prove2me | solution 1 for BooleanIsoperimetry.paired_step_cost_nonincrease
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:43:20.096212+00:00
-- url     : https://prove2.me/submissions/b7326e5d-0155-402b-a233-929b1054e962

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
public import Theorems.Thm_BooleanIsoperimetry_paired_coordinate_step_cost_nonincrease

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
    PairShadowCost N A' B' ≤ PairShadowCost N A B := by
  cases step with
  | coord i A' B' hA hB =>
      exact paired_coordinate_step_cost_nonincrease hA hB
  | cascade A' B' hTerm hTarget hTotal hCost hProgress =>
      exact hCost
end BooleanIsoperimetry
