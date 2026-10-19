-- Prove2me | solution 1 for ExplicitPNT.DusartTable1.Modules.Region100
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-18T13:12:15.84498+00:00
-- url     : https://prove2.me/submissions/28548f65-a21c-46bb-8e79-54fffcf5e98b

import Definitions.Def_DusartTable1ZeroRanges_433_20261018
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_ImprovedRegion
import Theorems.Thm_TaoFivePrimes_rh_verified_block_14_1e2

set_option autoImplicit false
set_option maxHeartbeats 1000000
open ExplicitPNT.DusartTable1

namespace ExplicitPNT.DusartTable1

private theorem zeta_seven_eighths : ∀ (s : ℂ) (hs : (7 / 8 : ℝ) < s.re),
    riemannZeta s ≠ 0 :=
  ExplicitPNT.DusartTable1.Modules.ImprovedRegion.1

private theorem log_fourteen_lower : (13 / 5 : ℝ) < Real.log 14 :=
  ExplicitPNT.DusartTable1.Modules.ImprovedRegion.2.1

private theorem log_hundred_lower : (23 / 5 : ℝ) < Real.log 100 := by
  have he : Real.exp (1 : ℝ) < (68 / 25 : ℝ) := by
    have h := Real.exp_one_lt_d9
    norm_num at h
    linarith
  have hp := pow_lt_pow_left₀ he (Real.exp_pos 1).le (by norm_num : (23 : ℕ) ≠ 0)
  have hpow : (Real.exp (1 : ℝ)) ^ 23 = Real.exp 23 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [hpow] at hp
  have h23 : Real.exp (23 : ℝ) < 100 ^ 5 := hp.trans (by norm_num)
  have hscale : Real.exp (23 / 5 : ℝ) ^ 5 = Real.exp 23 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hsmall : Real.exp (23 / 5 : ℝ) < 100 := by
    apply (pow_lt_pow_iff_left₀ (Real.exp_pos _).le (by norm_num) (by norm_num : (5 : ℕ) ≠ 0)).mp
    rwa [hscale]
  exact (Real.lt_log_iff_exp_lt (by norm_num)).2 hsmall

private theorem region100_positive (s : ℂ) (ht : 4 ≤ s.im)
    (hσ : 1 - 1 / ((7 / 4 : ℝ) * Real.log s.im) < s.re) :
    riemannZeta s ≠ 0 := by
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hlog4 : (1 : ℝ) ≤ Real.log 4 := by
    have h := Real.log_pow (2 : ℝ) 2
    norm_num at h
    linarith
  have hlog : (1 : ℝ) ≤ Real.log s.im :=
    hlog4.trans (Real.log_le_log (by norm_num) ht)
  have hden : (1 : ℝ) < (7 / 4) * Real.log s.im := by linarith
  have hinv : 1 / ((7 / 4 : ℝ) * Real.log s.im) < 1 :=
    (div_lt_one (by linarith)).2 hden
  have hpos : 0 < s.re := by linarith
  by_cases hge : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re hge
  have hlt : s.re < 1 := lt_of_not_ge hge
  by_cases hhigh : 100 < s.im
  · have hlog100 : (23 / 5 : ℝ) < Real.log s.im :=
      log_hundred_lower.trans_le (Real.log_le_log (by norm_num) hhigh.le)
    have h8 : (8 : ℝ) < (7 / 4) * Real.log s.im := by linarith
    have hinv8 : 1 / ((7 / 4 : ℝ) * Real.log s.im) < (1 / 8 : ℝ) := by
      apply (div_lt_iff₀ (by linarith : (0 : ℝ) < (7 / 4) * Real.log s.im)).2
      linarith
    exact zeta_seven_eighths s (by linarith)
  · by_cases h14 : 14 ≤ s.im
    · intro hz
      have hhalf := TaoFivePrimes.rh_verified_block_14_1e2 s hz hpos hlt h14
        (by norm_num; exact le_of_not_gt hhigh)
      have hlog14 : (13 / 5 : ℝ) < Real.log s.im :=
        log_fourteen_lower.trans_le (Real.log_le_log (by norm_num) h14)
      have h2 : (2 : ℝ) < (7 / 4) * Real.log s.im := by linarith
      have hinv2 : 1 / ((7 / 4 : ℝ) * Real.log s.im) < (1 / 2 : ℝ) := by
        apply (div_lt_iff₀ (by linarith : (0 : ℝ) < (7 / 4) * Real.log s.im)).2
        linarith
      linarith
    · exact TaoFivePrimes.zeta_ne_zero_strip_im_two_to_fourteen s hpos hlt
        (by linarith) (le_of_not_ge h14)

private theorem region100 (s : ℂ) (ht : 2 * Real.pi < |s.im|)
    (hσ : 1 - 1 / ((7 / 4 : ℝ) * Real.log |s.im|) < s.re) :
    riemannZeta s ≠ 0 := by
  have ht4 : 4 ≤ |s.im| := by linarith [Real.pi_gt_three]
  by_cases hpos : 0 ≤ s.im
  · rw [abs_of_nonneg hpos] at ht4 hσ
    exact region100_positive s ht4 hσ
  · have him : (star s).im = |s.im| := by
      simp only [Complex.star_def, Complex.conj_im]
      rw [abs_of_neg (lt_of_not_ge hpos)]
    have hre : (star s).re = s.re := by simp
    have hn := region100_positive (star s)
      (by simpa only [him] using ht4) (by simpa only [him, hre] using hσ)
    intro hz
    apply hn
    change riemannZeta ((starRingEnd ℂ) s) = 0
    rw [riemannZeta_conj, hz, map_zero]

end ExplicitPNT.DusartTable1

theorem solution :
(
    (23 / 5 : ℝ) < Real.log 100
) ∧
(
    ∀ (s : ℂ) (ht : 4 ≤ s.im)
    (hσ : 1 - 1 / ((7 / 4 : ℝ) * Real.log s.im) < s.re),
    riemannZeta s ≠ 0
) ∧
(
    ∀ (s : ℂ) (ht : 2 * Real.pi < |s.im|)
    (hσ : 1 - 1 / ((7 / 4 : ℝ) * Real.log |s.im|) < s.re),
    riemannZeta s ≠ 0
) := by
  exact ⟨log_hundred_lower, region100_positive, region100⟩
