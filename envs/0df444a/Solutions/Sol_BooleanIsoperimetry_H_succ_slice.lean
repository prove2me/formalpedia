-- Prove2me | solution 1 for BooleanIsoperimetry.H_succ_slice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:31:53.8457+00:00
-- url     : https://prove2.me/submissions/3252539b-5084-449b-b3e4-f810cbdd3697

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
public import Theorems.Thm_BooleanIsoperimetry_neighborhood_succ
public import Theorems.Thm_BooleanIsoperimetry_H_le_cube
public import Theorems.Thm_BooleanIsoperimetry_card_initSeg_union
public import Theorems.Thm_BooleanIsoperimetry_neighborhood_initSeg_eq
public import Theorems.Thm_BooleanIsoperimetry_slice0_initSeg_eq
public import Theorems.Thm_BooleanIsoperimetry_slice1_initSeg_eq
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n k : ℕ} :
    H (n + 1) k =
      max (H n (slice0 (simplicialInitSeg (n + 1) k)).card)
          (slice1 (simplicialInitSeg (n + 1) k)).card +
      max (H n (slice1 (simplicialInitSeg (n + 1) k)).card)
          (slice0 (simplicialInitSeg (n + 1) k)).card := by
  let A : Finset (Cube (n + 1)) := simplicialInitSeg (n + 1) k
  have hslice0 : slice0 A = simplicialInitSeg n (slice0 A).card := by
    simpa [A] using (slice0_initSeg_eq (n := n) (k := k))
  have hslice1 : slice1 A = simplicialInitSeg n (slice1 A).card := by
    simpa [A] using (slice1_initSeg_eq (n := n) (k := k))
  have hcard0 : (slice0 A).card ≤ 2 ^ n := by
    simpa using (Finset.card_le_univ (s := slice0 A))
  have hcard1 : (slice1 A).card ≤ 2 ^ n := by
    simpa using (Finset.card_le_univ (s := slice1 A))
  have h0 :
      (neighborhood 1 (slice0 A) ∪ slice1 A).card =
        max (H n (slice0 A).card) (slice1 A).card := by
    have hsets :
        neighborhood 1 (slice0 A) ∪ slice1 A =
          neighborhood 1 (simplicialInitSeg n (slice0 A).card) ∪
            simplicialInitSeg n (slice1 A).card :=
      congrArg₂ (· ∪ ·) (congrArg (neighborhood 1) hslice0) hslice1
    calc
      (neighborhood 1 (slice0 A) ∪ slice1 A).card =
          (neighborhood 1 (simplicialInitSeg n (slice0 A).card) ∪
            simplicialInitSeg n (slice1 A).card).card := congrArg Finset.card hsets
      _ = (simplicialInitSeg n (H n (slice0 A).card) ∪
            simplicialInitSeg n (slice1 A).card).card := by
            rw [neighborhood_initSeg_eq]
      _ = max (H n (slice0 A).card) (slice1 A).card :=
            card_initSeg_union (H_le_cube _ _) hcard1
  have h1 :
      (neighborhood 1 (slice1 A) ∪ slice0 A).card =
        max (H n (slice1 A).card) (slice0 A).card := by
    have hsets :
        neighborhood 1 (slice1 A) ∪ slice0 A =
          neighborhood 1 (simplicialInitSeg n (slice1 A).card) ∪
            simplicialInitSeg n (slice0 A).card :=
      congrArg₂ (· ∪ ·) (congrArg (neighborhood 1) hslice1) hslice0
    calc
      (neighborhood 1 (slice1 A) ∪ slice0 A).card =
          (neighborhood 1 (simplicialInitSeg n (slice1 A).card) ∪
            simplicialInitSeg n (slice0 A).card).card := congrArg Finset.card hsets
      _ = (simplicialInitSeg n (H n (slice1 A).card) ∪
            simplicialInitSeg n (slice0 A).card).card := by
            rw [neighborhood_initSeg_eq]
      _ = max (H n (slice1 A).card) (slice0 A).card :=
            card_initSeg_union (H_le_cube _ _) hcard0
  change (neighborhood 1 A).card =
    max (H n (slice0 A).card) (slice1 A).card +
      max (H n (slice1 A).card) (slice0 A).card
  rw [neighborhood_succ A, h0, h1]
end BooleanIsoperimetry
