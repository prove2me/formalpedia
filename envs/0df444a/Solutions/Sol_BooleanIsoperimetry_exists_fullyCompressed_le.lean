-- Prove2me | solution 1 for BooleanIsoperimetry.exists_fullyCompressed_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:45:41.630649+00:00
-- url     : https://prove2.me/submissions/c95184dc-fd97-4f22-9f90-41cf624475f6

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
public import Theorems.Thm_BooleanIsoperimetry_simplicialInitSeg_neighborhood_le_of_lowerSaturated
public import Theorems.Thm_BooleanIsoperimetry_simplicialInitSeg_isFullyCompressed
public import Theorems.Thm_BooleanIsoperimetry_exists_lowerSatDownFixed_le_aux
public import Theorems.Thm_BooleanIsoperimetry_card_le_two_pow
public import Theorems.Thm_BooleanIsoperimetry_card_simplicialInitSeg


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} (A : Finset (Cube N)) :
    ∃ C : Finset (Cube N), IsFullyCompressed C ∧ C.card = A.card ∧
      (neighborhood 1 C).card ≤ (neighborhood 1 A).card := by
  obtain ⟨A₁, _hdf, hls, hc, hn⟩ :=
    exists_lowerSatDownFixed_le_aux (compressionPotential A) A rfl
  refine ⟨simplicialInitSeg N A₁.card, simplicialInitSeg_isFullyCompressed, ?_, ?_⟩
  · rw [card_simplicialInitSeg, min_eq_left (card_le_two_pow A₁), hc]
  · exact le_trans (simplicialInitSeg_neighborhood_le_of_lowerSaturated hls) hn
end BooleanIsoperimetry
