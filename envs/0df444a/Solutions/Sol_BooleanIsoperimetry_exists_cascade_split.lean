-- Prove2me | solution 1 for BooleanIsoperimetry.exists_cascade_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:28:45.055558+00:00
-- url     : https://prove2.me/submissions/8e03d960-1b2e-4a55-bd3a-c1e03deb82bf

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Nat.Choose.Sum
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Theorems.Thm_BooleanIsoperimetry_exists_isBinomialCascade
public import Theorems.Thm_BooleanIsoperimetry_cascade_slice_add
public import Theorems.Thm_BooleanIsoperimetry_cascadeSlice0Value_le
public import Theorems.Thm_BooleanIsoperimetry_cascadeSlice1Value_le

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n k : ℕ) (hk : k ≤ 2 ^ (n + 1)) :
    ∃ p q, p ≤ 2 ^ n ∧ q ≤ 2 ^ n ∧ p + q = k ∧ CascadeSplit n k p q := by
  obtain ⟨r, t, hcasc⟩ := exists_isBinomialCascade n k hk
  refine ⟨cascadeSlice0Value n r t, cascadeSlice1Value n r t,
    cascadeSlice0Value_le hcasc, cascadeSlice1Value_le hcasc,
    cascade_slice_add hcasc, r, t, hcasc, rfl, rfl⟩
end BooleanIsoperimetry
