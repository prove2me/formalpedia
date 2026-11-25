-- Prove2me | solution 1 for FrontierMathLean.dimitrovConjecture3_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:59:10.138289+00:00
-- url     : https://prove2.me/submissions/d8c0d088-d798-4e3a-8c97-0aa72fdeae62

import Definitions.Def_FrontierMathLean_DimitrovConjecture1
import Definitions.Def_FrontierMathLean_NesbittRatioInequality
import Definitions.Def_FrontierMathLean_DimitrovConjecture3
import Theorems.Thm_FrontierMathLean_nesbitt_paper_bound_eq_normalized
import Theorems.Thm_FrontierMathLean_one_add_le_dedekindPsi
import Theorems.Thm_FrontierMathLean_one_add_le_sigmaOne
import Theorems.Thm_FrontierMathLean_three_term_nesbitt_power_inequality
import Theorems.Thm_FrontierMathLean_totient_le_sub_one


set_option autoImplicit false
open scoped ArithmeticFunction.sigma
open FrontierMathLean
namespace FrontierMathLean
theorem _root_.solution (k n : ℕ) (_hk : 1 ≤ k) (hn : 2 ≤ n) :
    (4 * ((n : ℝ) + 1) ^ (2 * k)
          + (((n : ℝ) ^ 2 - 1) ^ k)
          + ((n : ℝ) - 1) ^ (2 * k)) /
        (2 * (((n : ℝ) + 1) ^ (2 * k)
          + (((n : ℝ) ^ 2 - 1) ^ k))) ≤
      (n.totient : ℝ) ^ k /
          ((dedekindPsi n : ℝ) ^ k
            + (ArithmeticFunction.sigma 1 n : ℝ) ^ k) +
        (dedekindPsi n : ℝ) ^ k /
          ((n.totient : ℝ) ^ k
            + (ArithmeticFunction.sigma 1 n : ℝ) ^ k) +
        (ArithmeticFunction.sigma 1 n : ℝ) ^ k /
          ((n.totient : ℝ) ^ k + (dedekindPsi n : ℝ) ^ k) := by
  have hnpos : 0 < n := by omega
  have hcast_sub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have htotient_pos_nat : 0 < n.totient := Nat.totient_pos.mpr hnpos
  have htotient_pos : (0 : ℝ) < n.totient := by
    exact_mod_cast htotient_pos_nat
  have htotient_le : (n.totient : ℝ) ≤ (n : ℝ) - 1 := by
    rw [← hcast_sub]
    exact_mod_cast totient_le_sub_one hn
  have hu : (0 : ℝ) < (n : ℝ) - 1 := by
    rw [← hcast_sub]
    exact_mod_cast (show 0 < n - 1 by omega)
  have hv : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have huv : (n : ℝ) - 1 ≤ (n : ℝ) + 1 := by linarith
  have hpsi : (n : ℝ) + 1 ≤ dedekindPsi n := by
    exact_mod_cast one_add_le_dedekindPsi hn
  have hsigma : (n : ℝ) + 1 ≤ ArithmeticFunction.sigma 1 n := by
    exact_mod_cast one_add_le_sigmaOne hn
  have hfactor : (n : ℝ) ^ 2 - 1 = ((n : ℝ) - 1) * ((n : ℝ) + 1) := by
    ring
  rw [hfactor, nesbitt_paper_bound_eq_normalized hu hv k]
  exact three_term_nesbitt_power_inequality
    htotient_pos hu htotient_le huv hpsi hsigma
end FrontierMathLean
