-- Prove2me | solution 1 for BooleanIsoperimetry.hDist_embed0_embed0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:27:04.616619+00:00
-- url     : https://prove2.me/submissions/2fb0ba1b-ae1a-4f9d-b3dd-3faafde14553

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
    hDist (embed0 x) (embed0 y) = hDist x y := by
  unfold hDist
  convert Finset.card_image_of_injective _ (Fin.castSucc_injective n) using 2; ext
  simp +decide only [symmDiff, Finset.sup_eq_union', Finset.mem_union, Finset.mem_sdiff,
    Finset.mem_image]
  unfold embed0; aesop
end BooleanIsoperimetry
