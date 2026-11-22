-- Prove2me | solution 1 for BooleanIsoperimetry.card_eq_sum_card_filter_layer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:35:08.965842+00:00
-- url     : https://prove2.me/submissions/e559f367-6c0b-459e-ae66-f10e8bfc1576

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
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} (A : Finset (Cube N)) :
    A.card = ∑ k ∈ Finset.range (N + 1), (A.filter (fun x => x.card = k)).card := by
  have H : Set.MapsTo (fun (x : Cube N) => x.card) ↑A ↑(Finset.range (N + 1)) := by
    intro x _
    simp only [mem_coe, mem_range]
    have h1 : x.card ≤ Fintype.card (Fin N) := Finset.card_le_univ x
    have h2 : Fintype.card (Fin N) = N := Fintype.card_fin N
    omega
  exact Finset.card_eq_sum_card_fiberwise H
end BooleanIsoperimetry
