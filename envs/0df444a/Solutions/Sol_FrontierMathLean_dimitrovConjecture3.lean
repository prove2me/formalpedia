-- Prove2me | solution 1 for FrontierMathLean.dimitrovConjecture3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:02:45.766363+00:00
-- url     : https://prove2.me/submissions/c0312010-8f80-4925-a887-100ee4240aab

import Definitions.Def_FrontierMathLean_DimitrovConjecture1
import Definitions.Def_FrontierMathLean_NesbittRatioInequality
import Definitions.Def_FrontierMathLean_DimitrovConjecture3
import Theorems.Thm_FrontierMathLean_dimitrovConjecture3_real

set_option autoImplicit false
open scoped ArithmeticFunction.sigma
open FrontierMathLean
namespace FrontierMathLean
theorem _root_.solution (k n : ℕ) (hk : 1 ≤ k) (hn : 2 ≤ n) :
    (4 * ((n : ℚ) + 1) ^ (2 * k)
          + (((n : ℚ) ^ 2 - 1) ^ k)
          + ((n : ℚ) - 1) ^ (2 * k)) /
        (2 * (((n : ℚ) + 1) ^ (2 * k)
          + (((n : ℚ) ^ 2 - 1) ^ k))) ≤
      (n.totient : ℚ) ^ k /
          ((dedekindPsi n : ℚ) ^ k
            + (ArithmeticFunction.sigma 1 n : ℚ) ^ k) +
        (dedekindPsi n : ℚ) ^ k /
          ((n.totient : ℚ) ^ k
            + (ArithmeticFunction.sigma 1 n : ℚ) ^ k) +
        (ArithmeticFunction.sigma 1 n : ℚ) ^ k /
          ((n.totient : ℚ) ^ k + (dedekindPsi n : ℚ) ^ k) := by
  apply (Rat.cast_le (K := ℝ)).mp
  norm_num
  exact dimitrovConjecture3_real k n hk hn
end FrontierMathLean
