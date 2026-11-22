-- Prove2me | solution 1 for BooleanIsoperimetry.card_simplicialInitSeg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:29:29.536314+00:00
-- url     : https://prove2.me/submissions/a9cd93b7-6388-4628-9fdf-dae0a354fda7

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
public import Theorems.Thm_BooleanIsoperimetry_rank_lt_two_pow
public import Theorems.Thm_BooleanIsoperimetry_rank_injective
public import Theorems.Thm_BooleanIsoperimetry_rank_image_eq
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n k : ℕ} :
    (simplicialInitSeg n k).card = min k (2 ^ n) := by
  rw [← Finset.card_image_of_injective _ (rank_injective)]
  rw [show Finset.image rank (simplicialInitSeg n k) =
    Finset.filter (· < k) (Finset.range (2 ^ n)) from ?_]
  · rw [show { x ∈ Finset.range (2 ^ n) | x < k } =
      Finset.range (Min.min k (2 ^ n)) by ext x; aesop]
    simp +decide
  · ext
    simp only [simplicialInitSeg, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_range]
    constructor <;> intro h
    · exact ⟨ h.choose_spec.2 ▸ rank_lt_two_pow _, h.choose_spec.2 ▸ h.choose_spec.1 ⟩
    · obtain ⟨x, hx⟩ := Finset.mem_image.mp
        (rank_image_eq.symm ▸ Finset.mem_range.mpr h.1)
      use x
      aesop
end BooleanIsoperimetry
