-- Prove2me | solution 1 for BooleanIsoperimetry.slice_card_eq_cascade
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:35:06.375325+00:00
-- url     : https://prove2.me/submissions/e1b532f6-7802-4fb3-852e-7b0e35118c85

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Nat.Choose.Sum
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_succ
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_le_two_pow
public import Theorems.Thm_BooleanIsoperimetry_cascade_slice_add
public import Theorems.Thm_BooleanIsoperimetry_slice1_card_eq_cascade
public import Theorems.Thm_BooleanIsoperimetry_card_simplicialInitSeg
public import Theorems.Thm_BooleanIsoperimetry_slice_card_add


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n k p q : ℕ} (h : CascadeSplit n k p q) :
    (slice0 (simplicialInitSeg (n + 1) k)).card = p ∧
    (slice1 (simplicialInitSeg (n + 1) k)).card = q := by
  obtain ⟨r, t, hcasc, hp, hq⟩ := h
  have hq' : (slice1 (simplicialInitSeg (n + 1) k)).card = q := by
    rw [slice1_card_eq_cascade hcasc, hq]
  refine ⟨?_, hq'⟩
  have hpq : p + q = k := by rw [hp, hq]; exact cascade_slice_add hcasc
  -- k ≤ 2^(n+1), so the initial segment has cardinality exactly k
  obtain ⟨_, ht, hkeq, _⟩ := hcasc
  have hk_le : k ≤ 2 ^ (n + 1) := by
    have h2 := binomPrefix_le_two_pow (n + 1) (r + 1)
    have h3 := binomPrefix_succ (n + 1) r
    omega
  have hcard : (simplicialInitSeg (n + 1) k).card = k := by
    rw [card_simplicialInitSeg, min_eq_left hk_le]
  have hadd := slice_card_add (simplicialInitSeg (n + 1) k)
  omega
end BooleanIsoperimetry
