-- Prove2me | solution 1 for ExplicitPNT.DusartTable1.Modules.ImprovedRegion
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-18T13:05:28.30999+00:00
-- url     : https://prove2.me/submissions/7b6866cc-1afc-43f6-94f3-98ee3ea32b12

import Definitions.Def_DusartTable1ZeroRanges_433_20261018
import Definitions.Def_PNT_Kadiri_HeckeBridge_433_0010
import Theorems.Thm_OAI_SevenEighths_HeckeFamily_LFunction_ne_zero_of_seven_eighths_lt_re
import Theorems.Thm_TaoFivePrimes_zeta_ne_zero_strip_im_two_to_fourteen
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_TableTail

set_option autoImplicit false
set_option maxHeartbeats 1000000
open ExplicitPNT.DusartTable1

namespace ExplicitPNT.DusartTable1

private theorem zeta_seven_eighths (s : ℂ) (hs : (7 / 8 : ℝ) < s.re) :
    riemannZeta s ≠ 0 := by
  apply OAI.SevenEighths.HeckeDirichlet.zeta_seven_eighths_of_hecke _ s hs
  intro η z hz hpole
  apply OAI.SevenEighths.HeckeFamily.LFunction_ne_zero_of_seven_eighths_lt_re η hz
  rintro ⟨hη, hz1⟩
  rcases hpole with h | h
  · exact h hz1
  · exact h hη

private theorem log_fourteen_lower : (13 / 5 : ℝ) < Real.log 14 := by
  have he : Real.exp (1 : ℝ) < (68 / 25 : ℝ) := by
    have h := Real.exp_one_lt_d9
    norm_num at h
    linarith
  have hp := pow_lt_pow_left₀ he (Real.exp_pos 1).le (by norm_num : (13 : ℕ) ≠ 0)
  have hpow : (Real.exp (1 : ℝ)) ^ 13 = Real.exp 13 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [hpow] at hp
  have h13 : Real.exp (13 : ℝ) < 14 ^ 5 := hp.trans (by norm_num)
  have hscale : Real.exp (13 / 5 : ℝ) ^ 5 = Real.exp 13 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hsmall : Real.exp (13 / 5 : ℝ) < 14 := by
    apply (pow_lt_pow_iff_left₀ (Real.exp_pos _).le (by norm_num) (by norm_num : (5 : ℕ) ≠ 0)).mp
    rwa [hscale]
  exact (Real.lt_log_iff_exp_lt (by norm_num)).2 hsmall

private theorem improved_region_positive (s : ℂ) (ht : 2 ≤ s.im)
    (hσ : 1 - 1 / ((31 / 10 : ℝ) * Real.log s.im) < s.re) :
    riemannZeta s ≠ 0 := by
  by_cases hhigh : 14 < s.im
  · have hlog : (13 / 5 : ℝ) < Real.log s.im :=
      log_fourteen_lower.trans_le (Real.log_le_log (by norm_num) hhigh.le)
    have hden : (8 : ℝ) < (31 / 10) * Real.log s.im := by linarith
    have hinv : 1 / ((31 / 10 : ℝ) * Real.log s.im) < (1 / 8 : ℝ) := by
      apply (div_lt_iff₀ (by linarith : (0 : ℝ) < (31 / 10) * Real.log s.im)).2
      linarith
    exact zeta_seven_eighths s (by linarith)
  · by_cases hge : 1 ≤ s.re
    · exact riemannZeta_ne_zero_of_one_le_re hge
    · have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
        have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
        norm_num at h
        exact h
      have hlog : (1 / 2 : ℝ) ≤ Real.log s.im :=
        hlog2.trans (Real.log_le_log (by norm_num) ht)
      have hden : (1 : ℝ) < (31 / 10) * Real.log s.im := by linarith
      have hinv : 1 / ((31 / 10 : ℝ) * Real.log s.im) < 1 :=
        (div_lt_one (by linarith)).2 hden
      exact TaoFivePrimes.zeta_ne_zero_strip_im_two_to_fourteen s
        (by linarith) (lt_of_not_ge hge) ht (le_of_not_gt hhigh)

private theorem improved_region (s : ℂ) (ht : 2 * Real.pi < |s.im|)
    (hσ : 1 - 1 / ((31 / 10 : ℝ) * Real.log |s.im|) < s.re) :
    riemannZeta s ≠ 0 := by
  have ht2 : 2 ≤ |s.im| := by linarith [Real.pi_gt_three]
  by_cases hpos : 0 ≤ s.im
  · rw [abs_of_nonneg hpos] at ht2 hσ
    exact improved_region_positive s ht2 hσ
  · have him : (star s).im = |s.im| := by
      simp only [Complex.star_def, Complex.conj_im]
      rw [abs_of_neg (lt_of_not_ge hpos)]
    have hre : (star s).re = s.re := by simp
    have hn := improved_region_positive (star s)
      (by simpa only [him] using ht2) (by simpa only [him, hre] using hσ)
    intro hz
    apply hn
    change riemannZeta ((starRingEnd ℂ) s) = 0
    rw [riemannZeta_conj, hz, map_zero]

end ExplicitPNT.DusartTable1

theorem solution :
(
    ∀ (s : ℂ) (hs : (7 / 8 : ℝ) < s.re),
    riemannZeta s ≠ 0
) ∧
(
    (13 / 5 : ℝ) < Real.log 14
) ∧
(
    ∀ (s : ℂ) (ht : 2 ≤ s.im)
    (hσ : 1 - 1 / ((31 / 10 : ℝ) * Real.log s.im) < s.re),
    riemannZeta s ≠ 0
) ∧
(
    ∀ (s : ℂ) (ht : 2 * Real.pi < |s.im|)
    (hσ : 1 - 1 / ((31 / 10 : ℝ) * Real.log |s.im|) < s.re),
    riemannZeta s ≠ 0
) := by
  exact ⟨zeta_seven_eighths, log_fourteen_lower, improved_region_positive, improved_region⟩
