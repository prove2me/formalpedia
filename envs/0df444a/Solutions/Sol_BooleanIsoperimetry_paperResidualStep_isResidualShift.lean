-- Prove2me | solution 1 for BooleanIsoperimetry.paperResidualStep_isResidualShift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:43:15.9378+00:00
-- url     : https://prove2.me/submissions/d8f7e25f-3f69-44a3-8311-743dccabec84

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
public import Theorems.Thm_BooleanIsoperimetry_paperColexShiftMove_isResidualShift
public import Theorems.Thm_BooleanIsoperimetry_paperLevelBlockMove_card
public import Theorems.Thm_BooleanIsoperimetry_paperLevelBlockMove_neighborhood_card_le
public import Theorems.Thm_BooleanIsoperimetry_paperLevelBlockMove_potential_lt

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} {A A' : Finset (Cube N)}
    (h : IsPaperResidualStep A A') : IsDownFixedResidualShift A A' := by
  cases h with
  | colexShift hmove hnbhd _hdown _hlower =>
      exact paperColexShiftMove_isResidualShift hmove hnbhd
  | levelBlock hmove =>
      exact ⟨paperLevelBlockMove_card hmove, paperLevelBlockMove_neighborhood_card_le hmove,
        paperLevelBlockMove_potential_lt hmove⟩
end BooleanIsoperimetry
