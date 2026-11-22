-- Prove2me | solution 1 for BooleanIsoperimetry.binomPrefix_eq_two_pow_of_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:28:03.222832+00:00
-- url     : https://prove2.me/submissions/c4f86db8-e6f1-44d6-bc93-2aac75c65668

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Nat.Choose.Sum
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_mono
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_full
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_le_two_pow

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n r : ℕ) (h : n + 1 ≤ r) :
    binomPrefix n r = 2 ^ n := by
  apply le_antisymm
  · exact binomPrefix_le_two_pow n r
  · rw [← binomPrefix_full n]
    exact binomPrefix_mono n h
end BooleanIsoperimetry
