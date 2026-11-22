-- Prove2me | solution 1 for BooleanIsoperimetry.rank_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:36:27.425941+00:00
-- url     : https://prove2.me/submissions/f16aa958-3705-4de3-8084-ebaeb0e05caf

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
theorem _root_.solution {N : ℕ} : rank (∅ : Cube N) = 0 := by
  classical
  unfold rank
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro y _ h
  rcases h with ⟨hle, hnle⟩
  unfold simplicialLe at hle hnle
  rcases hle with h | ⟨hc, _⟩
  · simp at h
  · have hy : y = ∅ := Finset.card_eq_zero.mp hc
    subst hy
    exact hnle (Or.inr ⟨rfl, le_rfl⟩)
end BooleanIsoperimetry
