-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.PrimeCountingLemmas.upper_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:51:01.297752+00:00
-- url     : https://prove2.me/submissions/d950ffb2-674e-4d04-97ba-21d8dd45d8c2

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeRecipSum
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_PrimeCountingLemmas_centralBinom_le
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_PrimeCountingLemmas_primeCounting_le
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_PrimeCountingLemmas_real_ineq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Nat
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
open Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.PrimeCountingLemmas
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.PrimeCountingLemmas
theorem _root_.solution (n : ℕ) (hn : 10000 ≤ n) :
    (2 * (n : ℝ) + 1) ≤ 5 * (((upper n).card : ℝ) - 3) * Real.log (2 * n) := by
  have h1 : 4 ^ n < n * centralBinom n := Nat.four_pow_lt_mul_centralBinom n (by omega)
  have h2 := centralBinom_le n (by omega)
  set k := (upper n).card with hk
  set s := sqrt (2 * n) with hs
  set c := primeCounting s with hc
  have h3 : 4 ^ n < n * (((2 * n) ^ c * 4 ^ (2 * n / 3)) * (2 * n) ^ k) :=
    lt_of_lt_of_le h1 (Nat.mul_le_mul_left n h2)
  have h4 : (4 : ℝ) ^ n < n * (((2 * n) ^ c * 4 ^ (2 * n / 3)) * (2 * n) ^ k) := by
    exact_mod_cast h3
  have hn1 : (10000 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have h2n : (0 : ℝ) < 2 * n := by linarith
  have h5 := Real.log_lt_log (by positivity) h4
  rw [Real.log_mul hnpos.ne' (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow,
    Real.log_pow] at h5
  set L := Real.log (2 * n) with hLdef
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [hl4] at h5
  set l := Real.log 2 with hl
  have hl1 : 0.6931471803 < l := Real.log_two_gt_d9
  have hl2 : l < 0.6931471808 := Real.log_two_lt_d9
  set y := Real.sqrt (2 * n) with hy
  have hy2 : y ^ 2 = 2 * n := Real.sq_sqrt h2n.le
  have hy141 : 141 ≤ y := by
    apply Real.le_sqrt_of_sq_le
    linarith
  have hypos : 0 < y := by linarith
  have hsy : (s : ℝ) ≤ y := by
    have := Real.nat_sqrt_le_real_sqrt (a := 2 * n)
    simpa [hs, hy] using this
  have hs6 : 6 ≤ s := by
    rw [hs, Nat.le_sqrt]; omega
  have hcs : (c : ℝ) ≤ s / 3 + 3 := primeCounting_le s hs6
  have hLy : L = 2 * Real.log y := by
    rw [hLdef, ← hy2, Real.log_pow]; norm_num
  have hlogy : Real.log y ≤ 7 * l + y / 128 - 1 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < y / 128 by positivity)
    rw [Real.log_div hypos.ne' (by norm_num), show (128 : ℝ) = 2 ^ 7 by norm_num,
      Real.log_pow] at h
    push_cast at h
    linarith
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith)
  have hlogn : Real.log n ≤ L := Real.log_le_log hnpos (by linarith)
  have hdiv : (((2 * n / 3 : ℕ)) : ℝ) ≤ (2 * n : ℝ) / 3 := by
    have := (Nat.cast_div_le : (((2 * n) / 3 : ℕ) : ℝ) ≤ ((2 * n : ℕ) : ℝ) / ((3 : ℕ) : ℝ))
    simpa using this
  have hcL : (c : ℝ) * L ≤ (y / 3 + 3) * L := mul_le_mul_of_nonneg_right (by linarith) hL0
  have hdl : (((2 * n / 3 : ℕ)) : ℝ) * (2 * l) ≤ (2 * n : ℝ) / 3 * (2 * l) :=
    mul_le_mul_of_nonneg_right hdiv (by linarith)
  have key : y ^ 2 * l / 3 < (y / 3 + 4 + k) * L := by
    rw [hy2]
    nlinarith
  have := real_ineq hy141 hl1 hl2 (by linarith) key
  rw [hy2] at this
  exact this
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.PrimeCountingLemmas
