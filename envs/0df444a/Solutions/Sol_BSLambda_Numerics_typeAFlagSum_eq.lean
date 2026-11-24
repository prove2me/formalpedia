-- Prove2me | solution 1 for BSLambda.Numerics.typeAFlagSum_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:24:25.648649+00:00
-- url     : https://prove2.me/submissions/7cfaa32b-39e5-4ec7-b505-4d49c4214a94

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
theorem _root_.solution : Nat.choose 7004 3 + 3502 * Nat.choose 7003 2 = 143100492510 := by simp
end BSLambda.Numerics
