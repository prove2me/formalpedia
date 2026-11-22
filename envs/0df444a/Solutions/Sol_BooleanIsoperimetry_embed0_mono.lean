-- Prove2me | solution 1 for BooleanIsoperimetry.embed0_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:27:07.978789+00:00
-- url     : https://prove2.me/submissions/ff94e1a7-7d87-4b51-af47-47b83d2e13eb

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
public import Theorems.Thm_BooleanIsoperimetry_embed0_card
public import Theorems.Thm_BooleanIsoperimetry_embed0_cubeToNat
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n : ℕ} {x y : Cube n} (h : simplicialLe x y) :
    simplicialLe (embed0 x) (embed0 y) := by
  unfold simplicialLe at *
  rw [embed0_card, embed0_card, embed0_cubeToNat, embed0_cubeToNat]; aesop
end BooleanIsoperimetry
