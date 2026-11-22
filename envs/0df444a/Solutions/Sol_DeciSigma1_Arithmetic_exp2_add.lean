-- Prove2me | solution 1 for DeciSigma1.Arithmetic.exp2_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:34:30.893798+00:00
-- url     : https://prove2.me/submissions/3a69a8d4-c504-493b-b76a-a5db5ba24980

module
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Iterate
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Order.Monotone.Defs
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_ElementaryBounds

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Arithmetic
namespace DeciSigma1.Arithmetic
theorem _root_.solution (a b : ℕ) : exp2 (a + b) = exp2 a * exp2 b := pow_add _ _ _
end DeciSigma1.Arithmetic
