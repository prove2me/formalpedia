-- Prove2me | solution 1 for BooleanIsoperimetry.harper_theorem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T08:08:39.433773+00:00
-- url     : https://prove2.me/submissions/6f2b57e3-4faf-426d-bcd0-28eaaece9abc

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Harper
public import Theorems.Thm_BooleanIsoperimetry_initial_segment_optimal
public import Theorems.Thm_BooleanIsoperimetry_card_cube_le
public import Theorems.Thm_BooleanIsoperimetry_union_initSeg_card_le
public import Theorems.Thm_BooleanIsoperimetry_harper_base
public import Theorems.Thm_BooleanIsoperimetry_neighborhood_succ
public import Theorems.Thm_BooleanIsoperimetry_slice_card_add


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n : ℕ) (A : Finset (Cube n)) (k : ℕ) (hk : A.card = k) :
    (neighborhood 1 (simplicialInitSeg n k)).card ≤ (neighborhood 1 A).card := by
  revert A k
  induction n with
  | zero =>
    -- Base case: dimension 0
    exact harper_base
  | succ n ih =>
    -- Inductive step: n to n + 1
    intro A k hk
    let A0 := slice0 A
    let A1 := slice1 A
    let k0 := A0.card
    let k1 := A1.card
    -- Apply Inductive Hypothesis to the slices
    have ih0 := ih A0 k0 rfl
    have ih1 := ih A1 k1 rfl
    -- Use the decomposition of the neighborhood in n+1 dimensions
    calc (neighborhood 1 (simplicialInitSeg (n + 1) k)).card
      _ = (neighborhood 1 (simplicialInitSeg (n + 1) (k0 + k1))).card := by
          rw [← hk, ← slice_card_add A]
      _ ≤ (neighborhood 1 (simplicialInitSeg n k0) ∪ simplicialInitSeg n k1).card +
          (neighborhood 1 (simplicialInitSeg n k1) ∪ simplicialInitSeg n k0).card := by
          exact initial_segment_optimal k0 k1 (card_cube_le A0) (card_cube_le A1)
      _ ≤ (neighborhood 1 A0 ∪ A1).card + (neighborhood 1 A1 ∪ A0).card := by
          exact Nat.add_le_add
            (union_initSeg_card_le ih0 rfl (card_cube_le A1))
            (union_initSeg_card_le ih1 rfl (card_cube_le A0))
      _ = (neighborhood 1 A).card := by
          rw [neighborhood_succ A]
end BooleanIsoperimetry
