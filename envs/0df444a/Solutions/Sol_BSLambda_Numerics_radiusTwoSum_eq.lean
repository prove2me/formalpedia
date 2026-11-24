-- Prove2me | solution 1 for BSLambda.Numerics.radiusTwoSum_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:24:27.992703+00:00
-- url     : https://prove2.me/submissions/50a74132-7091-436b-88d0-d4d1f2040f0c

module
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial

set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.Numerics
attribute [local simp] Nat.choose_eq_descFactorial_div_factorial Nat.descFactorial Nat.factorial
namespace BSLambda.Numerics
theorem _root_.solution :
    9 * 2 ^ 20 * (∑ l ∈ Finset.range 9, Nat.choose 8 l * Nat.choose 28 (8 - l) * 2 ^ l) =
      1300311466573824 := by
  simp [Finset.sum_range_succ]
end BSLambda.Numerics
