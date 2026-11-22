-- Prove2me | solution 1 for BooleanIsoperimetry.hDist_insert_self_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:23:30.621623+00:00
-- url     : https://prove2.me/submissions/5678c5a1-4998-4a2a-9b05-79127acb6e86

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} (i : Fin N) (x : Cube N) : hDist (insert i x) x ≤ 1 := by
  unfold hDist
  have : symmDiff (insert i x) x ⊆ {i} := by
    intro j hj
    simp only [mem_symmDiff, mem_insert] at hj
    rw [mem_singleton]; tauto
  have hcard : (symmDiff (insert i x) x).card ≤ ({i} : Finset (Fin N)).card := card_le_card this
  rwa [card_singleton] at hcard
end BooleanIsoperimetry
