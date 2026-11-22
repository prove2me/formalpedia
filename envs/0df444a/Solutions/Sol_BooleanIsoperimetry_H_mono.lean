-- Prove2me | solution 1 for BooleanIsoperimetry.H_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:15:12.085389+00:00
-- url     : https://prove2.me/submissions/e3e7b8bd-f4e5-429f-9318-40132291af69

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n a b : ℕ} (h : a ≤ b) : H n a ≤ H n b := by
  unfold H
  apply Finset.card_le_card
  intro v hv
  rw [mem_neighborhood_iff] at hv ⊢
  rcases hv with ⟨u, hu, huv⟩
  refine ⟨u, ?_, huv⟩
  simp only [simplicialInitSeg, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
  exact Nat.lt_of_lt_of_le hu h
end BooleanIsoperimetry
