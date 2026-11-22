-- Prove2me | solution 1 for BooleanIsoperimetry.simplicialInitSeg_neighborhood_card_min
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:46:26.657752+00:00
-- url     : https://prove2.me/submissions/883ae8be-6009-410a-b8cd-d99def5b114c

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
public import Theorems.Thm_BooleanIsoperimetry_fullyCompressed_eq_initSeg
public import Theorems.Thm_BooleanIsoperimetry_exists_fullyCompressed_le

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} (A : Finset (Cube N)) :
    (neighborhood 1 (simplicialInitSeg N A.card)).card ≤ (neighborhood 1 A).card := by
  obtain ⟨C, hC, hCcard, hCnbhd⟩ := exists_fullyCompressed_le A
  have hCeq : C = simplicialInitSeg N C.card := fullyCompressed_eq_initSeg C hC
  rw [← hCcard, ← hCeq]
  exact hCnbhd
end BooleanIsoperimetry
