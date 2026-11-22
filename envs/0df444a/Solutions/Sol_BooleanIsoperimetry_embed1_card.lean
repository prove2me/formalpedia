-- Prove2me | solution 1 for BooleanIsoperimetry.embed1_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:15:28.31628+00:00
-- url     : https://prove2.me/submissions/fbb19866-ddb4-4eb4-9b07-297f67583935

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
theorem _root_.solution {n : ℕ} (x : Cube n) : (embed1 x).card = x.card + 1 := by
  unfold embed1
  simp [Finset.card_image_of_injective _ (Fin.castSucc_injective n)]
end BooleanIsoperimetry
