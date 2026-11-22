-- Prove2me | solution 1 for BooleanIsoperimetry.card_filter_card_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:28:50.400618+00:00
-- url     : https://prove2.me/submissions/82902ab5-4618-48ba-aac2-7a149903c1e3

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Nat.Choose.Sum
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_zero
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_succ
public import Theorems.Thm_BooleanIsoperimetry_card_filter_card_eq
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n c : ℕ) :
    (Finset.univ.filter (fun w : Cube n => w.card < c)).card = binomPrefix n c := by
  induction c with
  | zero => simp [binomPrefix_zero]
  | succ c ih =>
    have hsplit : (Finset.univ.filter (fun w : Cube n => w.card < c + 1))
        = (Finset.univ.filter (fun w : Cube n => w.card < c))
          ∪ (Finset.univ.filter (fun w : Cube n => w.card = c)) := by
      ext w; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      omega
    rw [hsplit, Finset.card_union_of_disjoint, ih, card_filter_card_eq, binomPrefix_succ]
    rw [Finset.disjoint_left]
    intro w hw hw'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw hw'
    omega
end BooleanIsoperimetry
