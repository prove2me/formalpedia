-- Prove2me | solution 1 for BSLambda.Numerics.depSumTwoTwo_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:24:50.104191+00:00
-- url     : https://prove2.me/submissions/ac9e2573-2412-4798-ae12-c45f464aa6c9

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
    (∑ s ∈ Finset.Icc 2 9, Nat.choose 9 s * Nat.choose 14002 (9 - s)) - 1 =
      753455972623601870517771054 := by
  simp [Finset.sum_Icc_succ_top]
end BSLambda.Numerics
