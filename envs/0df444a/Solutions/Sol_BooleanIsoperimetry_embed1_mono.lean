-- Prove2me | solution 1 for BooleanIsoperimetry.embed1_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:27:10.941954+00:00
-- url     : https://prove2.me/submissions/13a004de-fb36-460b-ad69-8681edf78ed5

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
public import Theorems.Thm_BooleanIsoperimetry_embed1_card
public import Theorems.Thm_BooleanIsoperimetry_embed1_cubeToNat
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n : ℕ} {x y : Cube n} (h : simplicialLe x y) :
    simplicialLe (embed1 x) (embed1 y) := by
  unfold simplicialLe at *
  cases h <;> simp_all +decide [embed1_card, embed1_cubeToNat]
end BooleanIsoperimetry
