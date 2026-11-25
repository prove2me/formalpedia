-- Prove2me | solution 1 for FrontierMathLean.dimitrovConjecture1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:02:43.442064+00:00
-- url     : https://prove2.me/submissions/afeb4bc8-707e-40b3-997a-6ce47a2a8778

import Definitions.Def_FrontierMathLean_ThreeTermInequality
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Definitions.Def_FrontierMathLean_DimitrovConjecture1
import Theorems.Thm_FrontierMathLean_dimitrovConjecture1_real

set_option autoImplicit false
open Finset
open scoped ArithmeticFunction.sigma
open FrontierMathLean
namespace FrontierMathLean
theorem _root_.solution (k n : ℕ) (hk : 1 ≤ k) (hn : 2 ≤ n) :
    (5 * ((n : ℚ) ^ 2 - 1) ^ k
          + 2 * ((n : ℚ) + 1) ^ (2 * k)
          + 2 * ((n : ℚ) - 1) ^ (2 * k)) /
        (((n : ℚ) ^ 2 - 1) ^ k) ≤
      ((n.totient : ℚ) ^ k + (dedekindPsi n : ℚ) ^ k
          + (ArithmeticFunction.sigma 1 n : ℚ) ^ k) *
        (((n.totient : ℚ) ^ k)⁻¹ + ((dedekindPsi n : ℚ) ^ k)⁻¹
          + ((ArithmeticFunction.sigma 1 n : ℚ) ^ k)⁻¹) := by
  apply (Rat.cast_le (K := ℝ)).mp
  norm_num
  exact dimitrovConjecture1_real k n hk hn
end FrontierMathLean
