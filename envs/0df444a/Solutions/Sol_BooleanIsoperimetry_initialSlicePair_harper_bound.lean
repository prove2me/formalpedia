-- Prove2me | solution 1 for BooleanIsoperimetry.initialSlicePair_harper_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:52:49.409181+00:00
-- url     : https://prove2.me/submissions/26209dd1-e669-48a3-846e-064f16da4a5b

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_MacaulayMin
public import Theorems.Thm_BooleanIsoperimetry_harper_macaulay_min
public import Theorems.Thm_BooleanIsoperimetry_neighborhood_initialSlicePair_card


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N a b : ℕ} (ha : a ≤ 2 ^ N) (hb : b ≤ 2 ^ N) :
    (neighborhood 1 (simplicialInitSeg (N + 1) (a + b))).card ≤
      (neighborhood 1 (initialSlicePair N a b)).card := by
  change H (N + 1) (a + b) ≤ (neighborhood 1 (initialSlicePair N a b)).card
  rw [neighborhood_initialSlicePair_card ha hb]
  exact harper_macaulay_min ha hb
end BooleanIsoperimetry
