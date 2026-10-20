-- Prove2me | solution 1 for FBAComp.AmazonGain.lemma_1_corrected
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T03:54:27.125066+00:00
-- url     : https://prove2.me/submissions/eb287939-9920-44f5-9283-73e59456449a

import Mathlib
import Theorems.Thm_FBAComp_AmazonGain_lemma_A_1
import Theorems.Thm_FBAComp_AmazonGain_lemma_A_2

namespace FBAComp.AmazonGain

lemma pS_gap (P : Params) (hP : P.Standing) (η T : ℝ) :
    pSF_star P η T - pSN_star P η =
      (T - P.c) * (8 - (1 + 3 * P.r) * P.β ^ 2 - (1 - P.r) * P.β ^ 4) /
          (2 * (1 - P.r) * (2 - P.β ^ 2) * (4 - (1 + P.r) * P.β ^ 2)) +
        (P.sA - P.sS) * (P.α * (8 - (3 + P.r) * P.β ^ 2) - η * P.β * (6 - (2 + P.r) * P.β ^ 2)) /
          (2 * (2 - P.β ^ 2) * (4 - (1 + P.r) * P.β ^ 2)) := by
  obtain ⟨_, _, hb0, hb1, hr0, hr1, _⟩ := hP
  have h1 : (1 - P.r) ≠ 0 := by nlinarith
  have h2 : (4 - (1 + P.r) * P.β ^ 2) ≠ 0 := by nlinarith
  have h3 : (2 - P.β ^ 2) ≠ 0 := by nlinarith
  simp only [pSN_star, pSF_star]
  generalize hD : (4 - (1 + P.r) * P.β ^ 2) = D at h2 ⊢
  generalize hE : (2 - P.β ^ 2) = E at h3 ⊢
  generalize hR : (1 - P.r) = R at h1 ⊢
  field_simp
  subst hD hE hR
  ring

end FBAComp.AmazonGain

open FBAComp.AmazonGain in
theorem solution (P : Params) (hP : P.Standing)
    (η wN pAN pSN T wF pAF pSF : ℝ) (hη : η ∈ Set.Ioo 0 P.α)
    (hN : IsEqN P η wN pAN pSN)
    (hF : IsFeeOptimal P η (profitSN P η pAN pSN) T wF pAF pSF)
    (hTc : P.c ≤ T) :
    pSN < pSF := by
  obtain ⟨-, rfl, rfl⟩ := (lemma_A_1 P hP η wN pAN pSN).mp hN
  obtain ⟨-, rfl, rfl⟩ := (lemma_A_2 P hP η T wF pAF pSF).mp hF.1
  have hgap := pS_gap P hP η T
  obtain ⟨ha0, ha1, hb0, hb1, hr0, hr1, hs0, hs1, _⟩ := hP
  obtain ⟨he0, he1⟩ := hη
  have hR : 0 < 1 - P.r := by linarith
  have hE : 0 < 2 - P.β ^ 2 := by nlinarith
  have hD : 0 < 4 - (1 + P.r) * P.β ^ 2 := by nlinarith
  have hK : 0 < 8 - (1 + 3 * P.r) * P.β ^ 2 - (1 - P.r) * P.β ^ 4 := by
    have hb2 : P.β ^ 2 < 1 := by nlinarith
    have hb4 : P.β ^ 4 < 1 := by nlinarith [pow_pos hb0 2]
    have : P.r * P.β ^ 2 < 1 := by nlinarith [pow_pos hb0 2]
    have : (1 - P.r) * P.β ^ 4 < 1 := by nlinarith [pow_pos hb0 4]
    nlinarith
  have hbr : 0 < (8 - (3 + P.r) * P.β ^ 2) - P.β * (6 - (2 + P.r) * P.β ^ 2) := by
    have h7 : 0 < 7 + P.β - 2 * P.β ^ 2 - P.r * P.β ^ 2 := by nlinarith [mul_pos hr0 (mul_pos hb0 hb0)]
    have := mul_pos (sub_pos.mpr hb1) h7
    nlinarith
  have hY : 0 < P.α * (8 - (3 + P.r) * P.β ^ 2) - η * P.β * (6 - (2 + P.r) * P.β ^ 2) := by
    have h8 : 0 < 8 - (3 + P.r) * P.β ^ 2 := by nlinarith
    nlinarith [mul_pos (sub_pos.mpr he1) h8, mul_pos he0 hbr]
  have t1 : 0 ≤ (T - P.c) * (8 - (1 + 3 * P.r) * P.β ^ 2 - (1 - P.r) * P.β ^ 4) /
      (2 * (1 - P.r) * (2 - P.β ^ 2) * (4 - (1 + P.r) * P.β ^ 2)) := by
    apply div_nonneg (mul_nonneg (by linarith) hK.le); positivity
  have t2 : 0 < (P.sA - P.sS) * (P.α * (8 - (3 + P.r) * P.β ^ 2) - η * P.β * (6 - (2 + P.r) * P.β ^ 2)) /
      (2 * (2 - P.β ^ 2) * (4 - (1 + P.r) * P.β ^ 2)) := by
    apply div_pos (mul_pos (by linarith) hY); positivity
  linarith
