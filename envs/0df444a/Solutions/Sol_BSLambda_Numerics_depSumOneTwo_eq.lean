-- Prove2me | solution 1 for BSLambda.Numerics.depSumOneTwo_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:24:40.402083+00:00
-- url     : https://prove2.me/submissions/7ee65344-4233-4376-b597-27c71d931527

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
    ∑ s ∈ Finset.Icc 2 5, Nat.choose 5 s * Nat.choose 14006 (9 - s) =
      209572451535510643927671555 := by
  simp [Finset.sum_Icc_succ_top]
end BSLambda.Numerics
