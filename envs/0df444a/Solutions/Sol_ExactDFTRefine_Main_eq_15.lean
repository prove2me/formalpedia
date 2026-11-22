-- Prove2me | solution 1 for ExactDFTRefine.Main.eq_15
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-22T23:19:09.568458+00:00
-- url     : https://prove2.me/submissions/db015965-04f9-4c04-a20e-d55d59a15248

import Mathlib
import Definitions.Def_ExactDFTRefine_Main_Moments

open ExactDFTRefine.Main

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 1000

theorem solution :
    gam ^ 97 ≤ 544 / 625 ∧ ((544 : ℝ) / 625) ^ 5 ≤ 1 / 2 ∧ eta ^ 40 ≤ 1 / 2 ∧
    gam ^ 11640 ≤ (2 : ℝ) ^ (-24 : ℤ) ∧ eta ^ 11640 ≤ (2 : ℝ) ^ (-291 : ℤ) ∧
    (∀ v : ℕ, (1 - eps) ^ v ≤ (1 + (v : ℝ) * eps)⁻¹) ∧
    (1 - eps) ^ 11640 + 2 * gam ^ 11640 + 2 * eta ^ 11640 ≤
      1 / (1 + 11640 * eps) + (2 : ℝ) ^ (-23 : ℤ) + (2 : ℝ) ^ (-290 : ℤ) ∧
    1 / (1 + 11640 * eps) + (2 : ℝ) ^ (-23 : ℤ) + (2 : ℝ) ^ (-290 : ℤ) < 1 ∧
    (195 : ℝ) / 10 ^ 9 <
      1 - (1 / (1 + 11640 * eps) + (2 : ℝ) ^ (-23 : ℤ) + (2 : ℝ) ^ (-290 : ℤ)) := by
  have hgam97 : gam ^ 97 ≤ (544 : ℝ) / 625 := by
    norm_num [gam]
  have hpow5 : ((544 : ℝ) / 625) ^ 5 ≤ 1 / 2 := by
    norm_num
  have heta40 : eta ^ 40 ≤ 1 / 2 := by
    norm_num [eta]
  have hgam0 : 0 ≤ gam := by norm_num [gam]
  have heta0 : 0 ≤ eta := by norm_num [eta]
  have hgam485 : gam ^ 485 ≤ 1 / 2 := by
    calc
      gam ^ 485 = (gam ^ 97) ^ 5 := by ring
      _ ≤ ((544 : ℝ) / 625) ^ 5 := by gcongr
      _ ≤ 1 / 2 := hpow5
  have hgam11640 : gam ^ 11640 ≤ (2 : ℝ) ^ (-24 : ℤ) := by
    calc
      gam ^ 11640 = (gam ^ 485) ^ 24 := by ring
      _ ≤ (1 / 2 : ℝ) ^ 24 := by gcongr
      _ = (2 : ℝ) ^ (-24 : ℤ) := by simp [zpow_neg, inv_pow, one_div]
  have heta11640 : eta ^ 11640 ≤ (2 : ℝ) ^ (-291 : ℤ) := by
    calc
      eta ^ 11640 = (eta ^ 40) ^ 291 := by ring
      _ ≤ (1 / 2 : ℝ) ^ 291 := by gcongr
      _ = (2 : ℝ) ^ (-291 : ℤ) := by simp [zpow_neg, inv_pow, one_div]
  have hbern : ∀ v : ℕ, (1 - eps) ^ v ≤ (1 + (v : ℝ) * eps)⁻¹ := by
    intro v
    induction v with
    | zero => norm_num [eps]
    | succ v ih =>
        have he0 : (0 : ℝ) < eps := by norm_num [eps]
        have he1 : (0 : ℝ) < 1 - eps := by norm_num [eps]
        have hden : (0 : ℝ) < 1 + (v : ℝ) * eps := by positivity
        have hden' : (0 : ℝ) < 1 + ((v + 1 : ℕ) : ℝ) * eps := by positivity
        rw [pow_succ]
        calc
          (1 - eps) ^ v * (1 - eps) ≤ (1 + (v : ℝ) * eps)⁻¹ * (1 - eps) := by
            gcongr
          _ ≤ (1 + ((v + 1 : ℕ) : ℝ) * eps)⁻¹ := by
            rw [inv_mul_eq_div, inv_eq_one_div]
            apply (div_le_div_iff₀ hden hden').2
            push_cast
            nlinarith [mul_nonneg (show 0 ≤ (v : ℝ) + 1 by positivity) (sq_nonneg eps)]
  refine ⟨hgam97, hpow5, heta40, hgam11640, heta11640, hbern, ?_, ?_, ?_⟩
  · have h2 : 2 * (2 : ℝ) ^ (-24 : ℤ) = (2 : ℝ) ^ (-23 : ℤ) := by
      rw [show (-24 : ℤ) = -23 - 1 by norm_num, zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
      norm_num
    have h3 : 2 * (2 : ℝ) ^ (-291 : ℤ) = (2 : ℝ) ^ (-290 : ℤ) := by
      rw [show (-291 : ℤ) = -290 - 1 by norm_num, zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
      norm_num
    calc
      (1 - eps) ^ 11640 + 2 * gam ^ 11640 + 2 * eta ^ 11640 ≤
          (1 + ((11640 : ℕ) : ℝ) * eps)⁻¹ +
            2 * (2 : ℝ) ^ (-24 : ℤ) + 2 * (2 : ℝ) ^ (-291 : ℤ) := by
              gcongr
              exact hbern 11640
      _ = 1 / (1 + 11640 * eps) + (2 : ℝ) ^ (-23 : ℤ) + (2 : ℝ) ^ (-290 : ℤ) := by
            rw [← h2, ← h3]
            norm_num only [Nat.cast_ofNat, one_div]
  · have hinv : (2 : ℝ) ^ (-290 : ℤ) = (1 / 2 : ℝ) ^ 290 := by
      simp [zpow_neg, inv_pow, one_div]
    rw [hinv]
    norm_num [eps]
  · have hinv : (2 : ℝ) ^ (-290 : ℤ) = (1 / 2 : ℝ) ^ 290 := by
      simp [zpow_neg, inv_pow, one_div]
    rw [hinv]
    norm_num [eps]
