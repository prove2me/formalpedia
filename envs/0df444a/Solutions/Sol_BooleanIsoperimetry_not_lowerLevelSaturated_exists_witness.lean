-- Prove2me | solution 1 for BooleanIsoperimetry.not_lowerLevelSaturated_exists_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:35:44.826182+00:00
-- url     : https://prove2.me/submissions/74d82571-3bfe-4ebd-9dff-8214efbfa47b

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
theorem _root_.solution {N : ℕ} {A : Finset (Cube N)}
    (h : ¬ IsLowerLevelSaturated A) :
    ∃ (T S : Cube N), T ∉ A ∧ S ∈ A ∧ T.card < S.card := by
  classical
  unfold IsLowerLevelSaturated at h
  push Not at h
  rcases h with ⟨T, S, hcard, hS, hT⟩
  exact ⟨T, S, hT, hS, hcard⟩
end BooleanIsoperimetry
