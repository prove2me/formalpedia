-- Prove2me | solution 1 for BooleanIsoperimetry.cascadeSlice1Value_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:18:58.468669+00:00
-- url     : https://prove2.me/submissions/9ace12b4-6681-4206-805f-3ed8892e370c

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Nat.Choose.Sum
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_le_two_pow
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_pred_add_choosePred

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n k r t : ℕ} (_ : IsBinomialCascade (n + 1) k r t) :
    cascadeSlice1Value n r t ≤ 2 ^ n := by
  have hadd := binomPrefix_pred_add_choosePred n r
  have hle := binomPrefix_le_two_pow n r
  unfold cascadeSlice1Value
  omega
end BooleanIsoperimetry
