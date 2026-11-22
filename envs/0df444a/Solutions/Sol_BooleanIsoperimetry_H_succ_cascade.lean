-- Prove2me | solution 1 for BooleanIsoperimetry.H_succ_cascade
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:35:53.75832+00:00
-- url     : https://prove2.me/submissions/714b8bcc-72a6-4064-b3e7-4fa479001aa9

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Nat.Choose.Sum
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Theorems.Thm_BooleanIsoperimetry_slice_card_eq_cascade
public import Theorems.Thm_BooleanIsoperimetry_H_succ_slice


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n k p q : ℕ} (h : CascadeSplit n k p q) :
    H (n + 1) k = max (H n p) q + max (H n q) p := by
  obtain ⟨h0, h1⟩ := slice_card_eq_cascade h
  rw [H_succ_slice, h0, h1]
end BooleanIsoperimetry
