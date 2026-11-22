-- Prove2me | solution 1 for BooleanIsoperimetry.hDist_embed1_embed1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:27:05.082938+00:00
-- url     : https://prove2.me/submissions/be8288d8-087d-4ebf-8d57-f3300107f9b2

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
theorem _root_.solution {n : ℕ} (x y : Cube n) :
    hDist (embed1 x) (embed1 y) = hDist x y := by
  unfold hDist embed1
  convert Finset.card_image_of_injective _ (Fin.castSucc_injective n) using 2
  ext
  simp +decide [symmDiff]
  aesop
end BooleanIsoperimetry
