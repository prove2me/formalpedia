-- Prove2me | solution 1 for ExplicitPNT.DusartTable1.Modules.LogarithmicZeroCount
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-18T13:25:15.075604+00:00
-- url     : https://prove2.me/submissions/15c1b1e3-4643-4e5b-a404-be8960ad4097

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
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_Region100

set_option autoImplicit false
set_option maxHeartbeats 1000000
open DusartSmoothing Complex Set
open ExplicitPNT.DusartTable1

namespace ExplicitPNT.DusartTable1

private theorem log_hundred_lower : (23 / 5 : ℝ) < Real.log 100 :=
  ExplicitPNT.DusartTable1.Modules.Region100.1

private theorem counting_majorant_log (t C : ℝ) (ht : 100 ≤ t)
    (hC : t / 6 + 31 ≤ C * t) :
    DusartSmoothing.RvM.countingMain t + 9 * Real.log (t + 5) + 79 ≤
      C * t * Real.log t := by
  have ht0 : 0 < t := by linarith
  have hl : 4 ≤ Real.log t := by
    have hh := log_hundred_lower.trans_le (Real.log_le_log (by norm_num) ht)
    linarith
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hsum : Real.log (t + 5) ≤ Real.log t + 1 := by
    calc
      _ ≤ Real.log (2 * t) := Real.log_le_log (by linarith) (by linarith)
      _ = Real.log 2 + Real.log t := Real.log_mul (by norm_num) ht0.ne'
      _ ≤ _ := by linarith
  have hratio : t / (2 * Real.pi) ≤ t / 6 := by
    apply div_le_div_of_nonneg_left ht0.le (by norm_num)
    linarith [Real.pi_gt_three]
  have hratio' : t / (2 * Real.pi) ≤ t := hratio.trans (by linarith)
  have hlog : Real.log (t / (2 * Real.pi)) - 1 ≤ Real.log t := by
    have hh := Real.log_le_log (by positivity) hratio'
    linarith
  have hmain : DusartSmoothing.RvM.countingMain t ≤ (t / 6) * Real.log t := by
    unfold DusartSmoothing.RvM.countingMain
    exact (mul_le_mul_of_nonneg_left hlog (by positivity)).trans
      (mul_le_mul_of_nonneg_right hratio (by linarith))
  have hh := mul_le_mul_of_nonneg_right hC (show 0 ≤ Real.log t by linarith)
  linarith only [hmain, hh, hsum, hl]

private theorem finite_zero_count_log_half (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (t : ℝ) (ht : 100 ≤ t) :
    finiteZeroCount Z DusartSmoothing.RvM.zeroMult Complex.im t ≤
      (1 / 2 : ℝ) * t * Real.log t := by
  exact (finite_actual_zero_count_bound Z hZ t (by linarith)).trans
    (counting_majorant_log t (1 / 2) ht (by linarith))

private theorem finite_zero_count_log_fifth (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (t : ℝ) (ht : 1000 ≤ t) :
    finiteZeroCount Z DusartSmoothing.RvM.zeroMult Complex.im t ≤
      (1 / 5 : ℝ) * t * Real.log t := by
  exact (finite_actual_zero_count_bound Z hZ t (by linarith)).trans
    (counting_majorant_log t (1 / 5) (by linarith) (by linarith))

private theorem finite_positive_zero_count_100 (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (hγ : ∀ ρ ∈ Z, ρ.im ≤ 100) :
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ)) ≤ 150 := by
  have hc := finite_actual_zero_count_bound Z hZ 100 (by norm_num)
  have he : finiteZeroCount Z DusartSmoothing.RvM.zeroMult Complex.im 100 =
      ∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    simp only [primeStep, if_pos (hγ ρ hρ), mul_one]
  rw [he] at hc
  have hl100 : Real.log (100 : ℝ) ≤ 5 := by
    apply (Real.log_le_iff_le_exp (by norm_num)).2
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 27 / 10)
      (show (27 / 10 : ℝ) ≤ Real.exp 1 by
        have he := Real.exp_one_gt_d9
        norm_num at he ⊢
        linarith) 5
    rw [← Real.exp_nat_mul] at hh
    norm_num at hh
    linarith
  have hl105 : Real.log (105 : ℝ) ≤ 5 := by
    apply (Real.log_le_iff_le_exp (by norm_num)).2
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 27 / 10)
      (show (27 / 10 : ℝ) ≤ Real.exp 1 by
        have he := Real.exp_one_gt_d9
        norm_num at he ⊢
        linarith) 5
    rw [← Real.exp_nat_mul] at hh
    norm_num at hh
    linarith
  have hl6 : 1 ≤ Real.log (2 * Real.pi) := by
    apply (Real.le_log_iff_exp_le (by positivity)).2
    have he := Real.exp_one_lt_d9
    norm_num at he
    linarith [Real.pi_gt_three]
  have hr : (100 : ℝ) / (2 * Real.pi) ≤ 16 := by
    apply (div_le_iff₀ (by positivity)).2
    linarith [Real.pi_gt_d2]
  have hlr : Real.log ((100 : ℝ) / (2 * Real.pi)) - 1 ≤ 3 := by
    rw [Real.log_div (by norm_num) (by positivity)]
    linarith
  have hm : DusartSmoothing.RvM.countingMain 100 ≤ 48 := by
    unfold DusartSmoothing.RvM.countingMain
    calc
      _ ≤ (100 / (2 * Real.pi)) * 3 := mul_le_mul_of_nonneg_left hlr (by positivity)
      _ ≤ 16 * 3 := mul_le_mul_of_nonneg_right hr (by norm_num)
      _ = 48 := by norm_num
  have hl105' : Real.log (105 : ℝ) ≤ (14 / 3 : ℝ) := by
    apply (Real.log_le_iff_le_exp (by norm_num)).2
    have he : (2718281828 / 10^9 : ℝ)^14 ≤ (Real.exp (14 / 3 : ℝ))^3 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2718281828 / 10^9)
        (show (2718281828 / 10^9 : ℝ) ≤ Real.exp 1 by
          have he := Real.exp_one_gt_d9
          norm_num at he ⊢
          linarith) 14
      rw [← Real.exp_nat_mul]
      rw [← Real.exp_nat_mul] at hh
      norm_num at hh ⊢
      exact hh
    have hn : (105 : ℝ)^3 ≤ (2718281828 / 10^9 : ℝ)^14 := by norm_num
    exact (pow_le_pow_iff_left₀ (by norm_num) (Real.exp_pos _).le (by norm_num : (3 : ℕ) ≠ 0)).mp (hn.trans he)
  have hlr' : Real.log ((100 : ℝ) / (2 * Real.pi)) - 1 ≤ (9 / 5 : ℝ) := by
    apply (sub_le_iff_le_add).2
    apply (Real.log_le_iff_le_exp (by positivity)).2
    have hp : (2 * Real.pi) ≥ (25 / 4 : ℝ) := by linarith [Real.pi_gt_d2]
    have hr' : (100 : ℝ) / (2 * Real.pi) ≤ 16 := by exact hr
    have h16 : (16 : ℝ) ≤ Real.exp (14 / 5 : ℝ) := by
      have hbase : (2718281828 / 10^9 : ℝ) ≤ Real.exp 1 := by
        have he := Real.exp_one_gt_d9
        norm_num at he ⊢
        linarith
      have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2718281828 / 10^9) hbase 14
      have hid : (Real.exp (14 / 5 : ℝ))^5 = Real.exp 14 := by rw [← Real.exp_nat_mul]; norm_num
      have hnum : (16 : ℝ)^5 ≤ (2718281828 / 10^9 : ℝ)^14 := by norm_num
      rw [← Real.exp_nat_mul] at hpow
      simp only [Nat.cast_ofNat, mul_one] at hpow
      exact (pow_le_pow_iff_left₀ (by norm_num) (Real.exp_pos _).le (by norm_num : (5 : ℕ) ≠ 0)).mp (by rw [hid]; exact hnum.trans hpow)
    simpa only [show (9 / 5 : ℝ) + 1 = 14 / 5 by norm_num] using hr'.trans h16
  have hm' : DusartSmoothing.RvM.countingMain 100 ≤ 29 := by
    unfold DusartSmoothing.RvM.countingMain
    calc
      _ ≤ (100 / (2 * Real.pi)) * (9 / 5 : ℝ) := mul_le_mul_of_nonneg_left hlr' (by positivity)
      _ ≤ 16 * (9 / 5 : ℝ) := mul_le_mul_of_nonneg_right hr (by norm_num)
      _ ≤ 29 := by norm_num
  norm_num at hc
  linarith only [hc, hm', hl105']

end ExplicitPNT.DusartTable1

theorem solution :
(
    ∀ (t C : ℝ) (ht : 100 ≤ t)
    (hC : t / 6 + 31 ≤ C * t),
    DusartSmoothing.RvM.countingMain t + 9 * Real.log (t + 5) + 79 ≤
      C * t * Real.log t
) ∧
(
    ∀ (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (t : ℝ) (ht : 100 ≤ t),
    finiteZeroCount Z DusartSmoothing.RvM.zeroMult Complex.im t ≤
      (1 / 2 : ℝ) * t * Real.log t
) ∧
(
    ∀ (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (t : ℝ) (ht : 1000 ≤ t),
    finiteZeroCount Z DusartSmoothing.RvM.zeroMult Complex.im t ≤
      (1 / 5 : ℝ) * t * Real.log t
) ∧
(
    ∀ (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (hγ : ∀ ρ ∈ Z, ρ.im ≤ 100),
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ)) ≤ 150
) := by
  exact ⟨counting_majorant_log, finite_zero_count_log_half, finite_zero_count_log_fifth, finite_positive_zero_count_100⟩
