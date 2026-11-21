-- Prove2me | solution 1 for Corless.folded_sizes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:41:33.500811+00:00
-- url     : https://prove2.me/submissions/55ae0d22-3fb0-47d8-81b6-75e2c3195e0e

module
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.CharP.Reduced
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Tactic.LinearCombination
public import Definitions.Def_LeanPool_CorlessNilpotent_Path
public import Definitions.Def_LeanPool_CorlessNilpotent_Parity
public import Theorems.Thm_Corless_two_le_pow

set_option autoImplicit true
@[expose] public section
public section
open Polynomial Finset
open Corless
namespace Corless
theorem _root_.solution (k : ℕ) :
    2 ^ (k + 1) - 1 = 2 ^ (k + 1) - 2 + 1 ∧
      2 ^ (k + 2) - 1 = 2 * (2 ^ (k + 1) - 2) + 3 := by
  have h := two_le_pow k
  constructor
  · omega
  · rw [pow_succ]
    omega
end Corless
