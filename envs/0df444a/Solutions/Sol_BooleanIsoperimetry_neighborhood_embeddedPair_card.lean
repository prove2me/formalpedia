-- Prove2me | solution 1 for BooleanIsoperimetry.neighborhood_embeddedPair_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:35:18.756718+00:00
-- url     : https://prove2.me/submissions/5494b159-0bfa-424b-8a1d-f4ba5b123c3d

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
public import Theorems.Thm_BooleanIsoperimetry_slice0_embeddedPair
public import Theorems.Thm_BooleanIsoperimetry_slice1_embeddedPair
public import Theorems.Thm_BooleanIsoperimetry_neighborhood_succ


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} (A B : Finset (Cube N)) :
    (neighborhood 1 (embeddedPair N A B)).card =
      (neighborhood 1 A ∪ B).card + (neighborhood 1 B ∪ A).card := by
  rw [neighborhood_succ, slice0_embeddedPair, slice1_embeddedPair]
end BooleanIsoperimetry
