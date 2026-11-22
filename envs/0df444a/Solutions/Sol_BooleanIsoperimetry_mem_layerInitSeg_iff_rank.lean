-- Prove2me | solution 1 for BooleanIsoperimetry.mem_layerInitSeg_iff_rank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:34:22.784532+00:00
-- url     : https://prove2.me/submissions/f2c84ad7-1b8f-42b3-91ec-19147a5e68d2

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Combinatorics.Colex
public import Mathlib.Combinatorics.SetFamily.Shadow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Mathlib.Combinatorics.SetFamily.KruskalKatona
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_KruskalKatona
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_card_le_rank
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open Finset.Colex
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N r t : ℕ} {x : Cube N} :
    x ∈ layerInitSeg N r t ↔
      x.card = r ∧ binomPrefix N r ≤ rank x ∧ rank x < binomPrefix N r + t := by
  simp only [layerInitSeg, simplicialInitSeg, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hrank, hcard⟩
    exact ⟨hcard, by simpa [hcard] using binomPrefix_card_le_rank x, hrank⟩
  · rintro ⟨hcard, hrank⟩
    exact ⟨hrank.2, hcard⟩
end BooleanIsoperimetry
