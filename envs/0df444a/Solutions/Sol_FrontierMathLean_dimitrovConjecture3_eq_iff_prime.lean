-- Prove2me | solution 1 for FrontierMathLean.dimitrovConjecture3_eq_iff_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:03:38.764287+00:00
-- url     : https://prove2.me/submissions/ea9df736-cee6-4c1b-9975-a676e977f9a8

import Definitions.Def_FrontierMathLean_DimitrovConjecture3
import Definitions.Def_FrontierMathLean_DimitrovConjecture3Equality
import Theorems.Thm_FrontierMathLean_dimitrovConjecture3_real_eq_iff_prime

set_option autoImplicit false
open scoped ArithmeticFunction.sigma
open FrontierMathLean
namespace FrontierMathLean
theorem _root_.solution
    (k n : ℕ) (hk : 1 ≤ k) (hn : 2 ≤ n) :
    ((4 * ((n : ℚ) + 1) ^ (2 * k)
            + (((n : ℚ) ^ 2 - 1) ^ k)
            + ((n : ℚ) - 1) ^ (2 * k)) /
          (2 * (((n : ℚ) + 1) ^ (2 * k)
            + (((n : ℚ) ^ 2 - 1) ^ k))) =
        (n.totient : ℚ) ^ k /
            ((dedekindPsi n : ℚ) ^ k
              + (ArithmeticFunction.sigma 1 n : ℚ) ^ k) +
          (dedekindPsi n : ℚ) ^ k /
            ((n.totient : ℚ) ^ k
              + (ArithmeticFunction.sigma 1 n : ℚ) ^ k) +
          (ArithmeticFunction.sigma 1 n : ℚ) ^ k /
            ((n.totient : ℚ) ^ k + (dedekindPsi n : ℚ) ^ k)) ↔
      n.Prime := by
  constructor
  · intro hEq
    apply (dimitrovConjecture3_real_eq_iff_prime k n hk hn).mp
    have hCast := congrArg (fun q : ℚ => (q : ℝ)) hEq
    norm_num at hCast
    exact hCast
  · intro hp
    have hReal := (dimitrovConjecture3_real_eq_iff_prime k n hk hn).mpr hp
    apply (Rat.cast_inj (α := ℝ)).mp
    norm_num
    exact hReal
end FrontierMathLean
