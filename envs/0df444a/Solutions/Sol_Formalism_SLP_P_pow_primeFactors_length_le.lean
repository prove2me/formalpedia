-- Prove2me | solution 1 for Formalism.SLP.P.pow_primeFactors_length_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:51:14.45442+00:00
-- url     : https://prove2.me/submissions/6fce3fb2-a80e-4f37-a9b2-6a3506297295

import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_OmegaPow
import Theorems.Thm_Formalism_SLP_P_two_pow_length_primeFactorsList_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.SLP Formalism.SLP.P
namespace Formalism.SLP.P
theorem _root_.solution : Formalism.SLP.OmegaPow := by
  intro n j hn hj
  set k := (Nat.primeFactorsList j).length
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hk : (2 : ℝ) ^ k ≤ j := by exact_mod_cast two_pow_length_primeFactorsList_le j hj

  have hklog : (k : ℝ) ≤ Real.logb 2 j := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) hj0]
    simpa [Real.rpow_natCast] using hk
  have hlogn : 0 ≤ Real.logb 2 n := Real.logb_nonneg (by norm_num) (by exact_mod_cast hn)

  have e1 : (n : ℝ) ^ k = (2 : ℝ) ^ ((k : ℝ) * Real.logb 2 n) := by
    rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hn0,
      Real.rpow_natCast]
  have e2 : (j : ℝ) ^ Real.logb 2 n = (2 : ℝ) ^ (Real.logb 2 j * Real.logb 2 n) := by
    rw [Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hj0]
  rw [e1, e2]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (mul_le_mul_of_nonneg_right hklog hlogn)
end Formalism.SLP.P
