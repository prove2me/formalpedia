-- Prove2me | solution 1 for BooleanIsoperimetry.H_ge_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:30:39.890253+00:00
-- url     : https://prove2.me/submissions/18c5134f-c86b-4918-a14e-4c68a80dc49f

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
public import Theorems.Thm_BooleanIsoperimetry_card_simplicialInitSeg
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n k : ℕ) (hk : k ≤ 2 ^ n) : k ≤ H n k := by
  exact le_trans (by simp +decide [card_simplicialInitSeg, hk]) <|
    Finset.card_mono <| show simplicialInitSeg n k ⊆ neighborhood 1 (simplicialInitSeg n k) from
      fun x hx => by
        rw [mem_neighborhood_iff]
        exact ⟨x, hx, by simp +decide [hDist]⟩
end BooleanIsoperimetry
