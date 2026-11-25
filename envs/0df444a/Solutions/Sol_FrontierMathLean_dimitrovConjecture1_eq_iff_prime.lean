-- Prove2me | solution 1 for FrontierMathLean.dimitrovConjecture1_eq_iff_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:03:05.458517+00:00
-- url     : https://prove2.me/submissions/1748a4d8-5e06-4d5e-b651-bbdc706b8d7f

import Definitions.Def_FrontierMathLean_DimitrovConjecture1
import Definitions.Def_FrontierMathLean_DimitrovConjecture1Equality
import Theorems.Thm_FrontierMathLean_dimitrovConjecture1_real_eq_iff_prime

set_option autoImplicit false
open Finset
open scoped ArithmeticFunction.sigma
open FrontierMathLean
namespace FrontierMathLean
theorem _root_.solution (k n : ℕ) (hk : 1 ≤ k) (hn : 2 ≤ n) :
    (5 * ((n : ℚ) ^ 2 - 1) ^ k
          + 2 * ((n : ℚ) + 1) ^ (2 * k)
          + 2 * ((n : ℚ) - 1) ^ (2 * k)) /
        (((n : ℚ) ^ 2 - 1) ^ k) =
      ((n.totient : ℚ) ^ k + (dedekindPsi n : ℚ) ^ k
          + (ArithmeticFunction.sigma 1 n : ℚ) ^ k) *
        (((n.totient : ℚ) ^ k)⁻¹ + ((dedekindPsi n : ℚ) ^ k)⁻¹
          + ((ArithmeticFunction.sigma 1 n : ℚ) ^ k)⁻¹) ↔
      n.Prime := by
  constructor
  · intro hEq
    apply (dimitrovConjecture1_real_eq_iff_prime k n hk hn).mp
    have hCast := congrArg (fun q : ℚ => (q : ℝ)) hEq
    norm_num at hCast
    exact hCast
  · intro hp
    have hReal := (dimitrovConjecture1_real_eq_iff_prime k n hk hn).mpr hp
    apply (Rat.cast_inj (α := ℝ)).mp
    norm_num
    exact hReal
end FrontierMathLean
