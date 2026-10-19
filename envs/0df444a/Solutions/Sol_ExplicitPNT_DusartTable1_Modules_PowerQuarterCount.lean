-- Prove2me | solution 1 for ExplicitPNT.DusartTable1.Modules.PowerQuarterCount
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-18T13:24:45.36072+00:00
-- url     : https://prove2.me/submissions/2f45e58f-d19b-4b1b-ac2a-bc0d4a26a5e8

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
open DusartSmoothing Complex Set
open ExplicitPNT.DusartTable1

namespace ExplicitPNT.DusartTable1

private theorem positive_zero_height_fourteen (ρ : ℂ)
    (hρ : DusartSmoothing.RvM.IsNontrivialZero ρ) (hi : 0 < ρ.im) :
    14 < ρ.im := by
  by_contra! h
  have hh := DusartSmoothing.RvM.nontrivial_zero_abs_height ρ hρ
  rw [abs_of_pos hi] at hh
  exact TaoFivePrimes.zeta_ne_zero_strip_im_two_to_fourteen ρ hρ.2.1 hρ.2.2
    (by linarith [Real.pi_gt_three]) h hρ.1

private theorem log_le_four_quarter (t : ℝ) (ht : 0 < t) :
    Real.log t ≤ 4 * t^(1 / 4 : ℝ) - 4 := by
  have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos ht (1 / 4 : ℝ))
  rw [Real.log_rpow ht] at h
  linarith

private theorem quarter_counting_majorant (t : ℝ) (ht : 14 ≤ t) :
    DusartSmoothing.RvM.countingMain t + 9 * Real.log (t + 5) + 79 ≤
      8 * t^(5 / 4 : ℝ) := by
  have ht0 : 0 < t := by linarith
  let u : ℝ := t^(1 / 4 : ℝ)
  have hu : 1 ≤ u := Real.one_le_rpow (by linarith) (by norm_num)
  have htprod : t^(5 / 4 : ℝ) = t * u := by
    dsimp [u]
    calc
      _ = t^((1 : ℝ) + 1 / 4) := by norm_num
      _ = t^(1 : ℝ) * t^(1 / 4 : ℝ) := Real.rpow_add ht0 _ _
      _ = _ := by rw [Real.rpow_one]
  have hyr : (t + 5)^(1 / 4 : ℝ) ≤ (3 / 2 : ℝ) * u := by
    calc
      _ ≤ (((3 / 2 : ℝ)^4) * t)^(1 / 4 : ℝ) :=
        Real.rpow_le_rpow (by linarith) (by norm_num; linarith) (by norm_num)
      _ = _ := by
        rw [Real.mul_rpow (by positivity) ht0.le, ← Real.rpow_natCast_mul (by norm_num)]
        norm_num [u]
  have hl := log_le_four_quarter t ht0
  have hly := log_le_four_quarter (t + 5) (by linarith)
  have hratio : t / (2 * Real.pi) ≤ t / 6 := by
    apply div_le_div_of_nonneg_left ht0.le (by norm_num)
    linarith [Real.pi_gt_three]
  have hratio' : t / (2 * Real.pi) ≤ t :=
    hratio.trans (by linarith)
  have hlog : Real.log (t / (2 * Real.pi)) - 1 ≤ 4 * u := by
    have h := Real.log_le_log (by positivity) hratio'
    dsimp [u]
    linarith
  have hmain : DusartSmoothing.RvM.countingMain t ≤ (2 / 3 : ℝ) * t * u := by
    unfold DusartSmoothing.RvM.countingMain
    calc
      _ ≤ (t / (2 * Real.pi)) * (4 * u) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ ≤ (t / 6) * (4 * u) := mul_le_mul_of_nonneg_right hratio (by positivity)
      _ = _ := by ring
  rw [htprod]
  have hmul : 14 * u ≤ t * u := mul_le_mul_of_nonneg_right ht (by linarith)
  nlinarith

private theorem finite_zero_count_quarter (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (t : ℝ) (ht : 4 ≤ t) :
    finiteZeroCount Z DusartSmoothing.RvM.zeroMult Complex.im t ≤ 8 * t^(5 / 4 : ℝ) := by
  by_cases h14 : 14 ≤ t
  · exact (finite_actual_zero_count_bound Z hZ t ht).trans (quarter_counting_majorant t h14)
  · have he : finiteZeroCount Z DusartSmoothing.RvM.zeroMult Complex.im t = 0 := by
      apply Finset.sum_eq_zero
      intro ρ hρ
      obtain ⟨hnt, hi⟩ := hZ ρ hρ
      have hh := positive_zero_height_fourteen ρ hnt hi
      simp only [primeStep, if_neg (show ¬ρ.im ≤ t by linarith), mul_zero]
    rw [he]
    positivity

end ExplicitPNT.DusartTable1

theorem solution :
(
    ∀ (ρ : ℂ)
    (hρ : DusartSmoothing.RvM.IsNontrivialZero ρ) (hi : 0 < ρ.im),
    14 < ρ.im
) ∧
(
    ∀ (t : ℝ) (ht : 0 < t),
    Real.log t ≤ 4 * t^(1 / 4 : ℝ) - 4
) ∧
(
    ∀ (t : ℝ) (ht : 14 ≤ t),
    DusartSmoothing.RvM.countingMain t + 9 * Real.log (t + 5) + 79 ≤
      8 * t^(5 / 4 : ℝ)
) ∧
(
    ∀ (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (t : ℝ) (ht : 4 ≤ t),
    finiteZeroCount Z DusartSmoothing.RvM.zeroMult Complex.im t ≤ 8 * t^(5 / 4 : ℝ)
) := by
  exact ⟨positive_zero_height_fourteen, log_le_four_quarter, quarter_counting_majorant, finite_zero_count_quarter⟩
