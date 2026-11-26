-- Prove2me | solution 1 for BandParity.eq_of_pow_four_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:52:40.876668+00:00
-- url     : https://prove2.me/submissions/6d6da44d-8038-4398-b619-6a19ef191681

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_BandParity_Basic
public import Theorems.Thm_BandParity_gi_sq

set_option autoImplicit true
@[expose] public section
public section
open BandParity
namespace BandParity
theorem _root_.solution {x : GaussianInt} (h : x ^ 4 = 1) :
    x = 1 ∨ x = gi ∨ x = -1 ∨ x = -gi := by
  have e : (x - 1) * (x + 1) * (x - gi) * (x + gi) = 0 := by
    linear_combination (1 - x ^ 2) * gi_sq + h
  rcases mul_eq_zero.1 e with e | e
  · rcases mul_eq_zero.1 e with e | e
    · rcases mul_eq_zero.1 e with e | e
      · exact Or.inl (sub_eq_zero.1 e)
      · exact Or.inr (Or.inr (Or.inl (eq_neg_of_add_eq_zero_left e)))
    · exact Or.inr (Or.inl (sub_eq_zero.1 e))
  · exact Or.inr (Or.inr (Or.inr (eq_neg_of_add_eq_zero_left e)))
end BandParity
