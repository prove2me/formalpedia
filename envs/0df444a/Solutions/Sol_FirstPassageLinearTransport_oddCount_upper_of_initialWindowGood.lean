-- Prove2me | solution 1 for FirstPassageLinearTransport.oddCount_upper_of_initialWindowGood
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:37:48.890928+00:00
-- url     : https://prove2.me/submissions/4c6c8b90-9014-4c7b-aa0a-de8c12e1504a

import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_ClockBudget
import Definitions.Def_FirstPassageLinearTransport_RawClockBudget
import Theorems.Thm_FirstPassageLinearTransport_centralOrbitScale_eq_two_rpow_neg_gap
import Theorems.Thm_FirstPassageLinearTransport_normalizedCorrection_nonneg
import Theorems.Thm_FirstPassageLinearTransport_orbit_eq_normalizedCorrection


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {eta : ℝ} {n k : ℕ}
    (hn : 0 < n) (hnGood : n ∈ initialWindowGood eta)
    (hk : k ≤ Nat.log 2 n) :
    (oddCount n k : ℝ) ≤
      (k : ℝ) / 2 + eta * Real.log n / Real.log 3 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hupper := (hnGood k hk).2
  have hmain :
      (n : ℝ) / (2 : ℝ) ^ k * (3 : ℝ) ^ oddCount n k ≤
        (orbit k n : ℝ) := by
    rw [orbit_eq_normalizedCorrection]
    have hcorr := normalizedCorrection_nonneg k n
    have hthree : 0 ≤ (3 : ℝ) ^ oddCount n k := by positivity
    exact mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right hcorr) hthree
  have hLU := hmain.trans hupper
  have hleftPos :
      0 < (n : ℝ) / (2 : ℝ) ^ k * (3 : ℝ) ^ oddCount n k := by
    positivity
  have hlogs := Real.log_le_log hleftPos hLU
  rw [Real.log_mul (div_ne_zero hnR.ne' (by positivity)) (by positivity),
    Real.log_div hnR.ne' (by positivity), Real.log_pow,
    Real.log_pow, centralOrbitScale_eq_two_rpow_neg_gap,
    Real.log_mul (Real.rpow_pos_of_pos (by norm_num) _).ne'
      (Real.rpow_pos_of_pos hnR _).ne',
    Real.log_rpow (by norm_num), Real.log_rpow hnR] at hlogs
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have ha0log : a0 * Real.log 2 = Real.log 3 / 2 := by
    unfold a0 logTwoThree
    field_simp [hlog2.ne']
  unfold driftGap at hlogs
  have hscaled :
      ((oddCount n k : ℝ) - (k : ℝ) / 2) * Real.log 3 ≤
        eta * Real.log n := by
    nlinarith
  have hdiff :
      (oddCount n k : ℝ) - (k : ℝ) / 2 ≤
        eta * Real.log n / Real.log 3 :=
    (le_div_iff₀ hlog3).2 hscaled
  linarith
end FirstPassageLinearTransport
