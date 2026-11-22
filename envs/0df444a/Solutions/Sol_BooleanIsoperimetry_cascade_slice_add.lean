-- Prove2me | solution 1 for BooleanIsoperimetry.cascade_slice_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:18:35.214308+00:00
-- url     : https://prove2.me/submissions/e826b034-42a8-4873-a751-298baa38d073

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Nat.Choose.Sum
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_pascal

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n k r t : ℕ} (h : IsBinomialCascade (n + 1) k r t) :
    cascadeSlice0Value n r t + cascadeSlice1Value n r t = k := by
  obtain ⟨_, ht, hk, _⟩ := h
  have hp := binomPrefix_pascal n r
  unfold cascadeSlice0Value cascadeSlice1Value
  omega
end BooleanIsoperimetry
