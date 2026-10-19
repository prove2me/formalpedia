-- Prove2me | solution 1 for ExplicitPNT.DusartTable1.Modules.RationalLogCertificates
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-18T13:30:33.152605+00:00
-- url     : https://prove2.me/submissions/f7e0b285-bf6c-4ed5-bee7-850e0c68e476

import Definitions.Def_DusartTable1ZeroRanges_433_20261018
import Theorems.Thm_ExplicitPNT_dusart_refined_psi_error_of_zero_free_region
import Theorems.Thm_ExplicitPNT_kadiri_zero_free_region_569693
import Definitions.Def_DusartThetaTable1Intervals
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic
import Definitions.Def_PNT_Kadiri_HeckeBridge_433_0010
import Theorems.Thm_OAI_SevenEighths_HeckeFamily_LFunction_ne_zero_of_seven_eighths_lt_re
import Theorems.Thm_TaoFivePrimes_zeta_ne_zero_strip_im_two_to_fourteen
import Theorems.Thm_TaoFivePrimes_rh_verified_block_14_1e2
import Definitions.Def_dusart_psi_433_20261014_PsiZeroSum
import Definitions.Def_dusart_psi_433_20261014_PsiComparison

set_option autoImplicit false
set_option maxHeartbeats 1000000
open ExplicitPNT.DusartTable1

namespace ExplicitPNT.DusartTable1

private theorem log_le_rational_of_certificate (x : ℝ) (m n : ℕ)
    (hx : 0 < x) (hn : 0 < n)
    (hnum : x^n ≤ (2718281828 / 10^9 : ℝ)^m) :
    Real.log x ≤ (m : ℝ) / n := by
  apply (Real.log_le_iff_le_exp hx).2
  have hbase : (2718281828 / 10^9 : ℝ) ≤ Real.exp 1 := by
    have hh := Real.exp_one_gt_d9
    norm_num at hh ⊢
    linarith
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2718281828 / 10^9) hbase m
  rw [← Real.exp_nat_mul] at hp
  simp only [mul_one] at hp
  have he : (Real.exp ((m : ℝ) / n))^n = Real.exp (m : ℝ) := by
    rw [← Real.exp_nat_mul]
    congr 1
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  apply (pow_le_pow_iff_left₀ hx.le (Real.exp_pos _).le hn.ne').mp
  rw [he]
  exact hnum.trans hp

private theorem log_nineteen_fourteen_le : Real.log (19 / 14 : ℝ) ≤ 1 / 3 := by
  simpa using log_le_rational_of_certificate (19 / 14) 1 3
    (by norm_num) (by norm_num) (by norm_num)

private theorem log_fourteen_upper : Real.log (14 : ℝ) ≤ 53 / 20 := by
  simpa using log_le_rational_of_certificate 14 53 20
    (by norm_num) (by norm_num) (by norm_num)

private theorem log_add_five_upper (t : ℝ) (ht : 14 ≤ t) :
    Real.log (t + 5) ≤ Real.log t + 1 / 3 := by
  have ht0 : 0 < t := by linarith
  calc
    _ ≤ Real.log ((19 / 14 : ℝ) * t) :=
      Real.log_le_log (by linarith) (by linarith)
    _ = Real.log (19 / 14 : ℝ) + Real.log t :=
      Real.log_mul (by norm_num) ht0.ne'
    _ ≤ _ := by linarith only [log_nineteen_fourteen_le]

end ExplicitPNT.DusartTable1

theorem solution :
(
    ∀ (x : ℝ) (m n : ℕ)
    (hx : 0 < x) (hn : 0 < n)
    (hnum : x^n ≤ (2718281828 / 10^9 : ℝ)^m),
    Real.log x ≤ (m : ℝ) / n
) ∧
(
    Real.log (19 / 14 : ℝ) ≤ 1 / 3
) ∧
(
    Real.log (14 : ℝ) ≤ 53 / 20
) ∧
(
    ∀ (t : ℝ) (ht : 14 ≤ t),
    Real.log (t + 5) ≤ Real.log t + 1 / 3
) := by
  exact ⟨log_le_rational_of_certificate, log_nineteen_fourteen_le, log_fourteen_upper, log_add_five_upper⟩
