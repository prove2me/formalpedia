-- Prove2me | solution 1 for BooleanIsoperimetry.lowCard_eq_initSeg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:31:26.225227+00:00
-- url     : https://prove2.me/submissions/bfae9d36-8bd2-40c0-8513-1c07d37f5114

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Nat.Choose.Sum
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Theorems.Thm_BooleanIsoperimetry_card_filter_card_lt
public import Theorems.Thm_BooleanIsoperimetry_downwardClosed_eq_initSeg
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n c : ℕ) :
    Finset.univ.filter (fun w : Cube n => w.card < c)
      = simplicialInitSeg n (binomPrefix n c) := by
  have hdc : ∀ x y, simplicialLe x y →
      y ∈ Finset.univ.filter (fun w : Cube n => w.card < c) →
      x ∈ Finset.univ.filter (fun w : Cube n => w.card < c) := by
    intro x y hxy hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    have : x.card ≤ y.card := by rcases hxy with h | ⟨h, _⟩ <;> omega
    omega
  have h := downwardClosed_eq_initSeg hdc
  rw [card_filter_card_lt] at h
  exact h
end BooleanIsoperimetry
