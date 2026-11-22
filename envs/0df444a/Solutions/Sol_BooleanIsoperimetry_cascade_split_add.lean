-- Prove2me | solution 1 for BooleanIsoperimetry.cascade_split_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:19:23.518407+00:00
-- url     : https://prove2.me/submissions/31cb9811-56eb-47cf-92b2-1bd2df01332a

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Nat.Choose.Sum
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Theorems.Thm_BooleanIsoperimetry_cascade_slice_add

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n k p q : ℕ} (h : CascadeSplit n k p q) : p + q = k := by
  obtain ⟨r, t, hcasc, hp, hq⟩ := h
  rw [hp, hq]
  exact cascade_slice_add hcasc
end BooleanIsoperimetry
