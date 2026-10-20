-- Prove2me | solution 1 for FBAComp.AmazonGain.proposition_1_i
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T03:55:23.387047+00:00
-- url     : https://prove2.me/submissions/699ebc4d-0baa-4eeb-b74c-bdbcc89667c5

import Mathlib
import Theorems.Thm_FBAComp_AmazonGain_lemma_A_1
import Theorems.Thm_FBAComp_AmazonGain_lemma_A_2

namespace FBAComp.AmazonGain


lemma quad_argmax (f : ℝ → ℝ) (a b k x0 : ℝ) (ha : 0 < a)
    (hf : ∀ x, f x = -a * x ^ 2 + b * x + k) :
    (∀ x, f x ≤ f x0) ↔ 2 * a * x0 = b := by
  constructor
  · intro h
    have h1 := h (b / (2 * a))
    rw [hf, hf] at h1
    have h2 : a * (x0 - b / (2 * a)) ^ 2 ≤ 0 := by
      have : a * (x0 - b / (2 * a)) ^ 2 = (-a * (b / (2 * a)) ^ 2 + b * (b / (2 * a)) + k) -
          (-a * x0 ^ 2 + b * x0 + k) := by
        field_simp; ring
      linarith
    have h3 : (x0 - b / (2 * a)) ^ 2 = 0 := by
      have := mul_nonneg ha.le (sq_nonneg (x0 - b / (2 * a)))
      have h4 : a * (x0 - b / (2 * a)) ^ 2 = 0 := le_antisymm h2 this
      rcases mul_eq_zero.mp h4 with h | h
      · linarith
      · exact h
    have h5 : x0 = b / (2 * a) := by nlinarith [pow_eq_zero_iff (n := 2) (two_ne_zero) |>.mp h3]
    rw [h5]; field_simp
  · intro h x
    rw [hf, hf]
    have : b = 2 * a * x0 := h.symm
    subst this
    nlinarith [mul_nonneg ha.le (sq_nonneg (x - x0))]

lemma nashN_iff (P : Params) (hr : P.r < 1) (η w pA pS : ℝ) :
    IsPriceNE_N P η w pA pS ↔
      (2 * pA = P.QA + P.β * pS + P.α * P.sA - η * P.sS + w + P.c + P.r * P.β * pS ∧
       2 * (1 - P.r) * pS = (1 - P.r) * (P.QS + P.β * pA + P.α * P.sS - η * P.sA) + P.g + P.c) := by
  unfold IsPriceNE_N PriceGame.IsNash
  simp only
  rw [quad_argmax (fun x => profitAN P η w x pS) 1
      (P.QA + P.β * pS + P.α * P.sA - η * P.sS + w + P.c + P.r * P.β * pS)
      (-(w + P.c) * (P.QA + P.β * pS + P.α * P.sA - η * P.sS) +
        P.r * pS * (P.QS - pS + P.α * P.sS - η * P.sA)) pA one_pos
      (by intro x; simp only [profitAN, qAN, qSN]; ring)]
  rw [quad_argmax (fun x => profitSN P η pA x) (1 - P.r)
      ((1 - P.r) * (P.QS + P.β * pA + P.α * P.sS - η * P.sA) + P.g + P.c)
      (-(P.g + P.c) * (P.QS + P.β * pA + P.α * P.sS - η * P.sA)) pS (by linarith)
      (by intro x; simp only [profitSN, qSN]; ring)]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩

lemma nashF_iff (P : Params) (hr : P.r < 1) (η T w pA pS : ℝ) :
    IsPriceNE_F P η T w pA pS ↔
      (2 * pA = P.QA + P.β * pS + P.α * P.sA - η * P.sA + w + P.c + P.β * (P.r * pS + T - P.c) ∧
       2 * (1 - P.r) * pS = (1 - P.r) * (P.QS + P.β * pA + P.α * P.sA - η * P.sA) + P.g + T) := by
  unfold IsPriceNE_F PriceGame.IsNash
  simp only
  rw [quad_argmax (fun x => profitAF P η T w x pS) 1
      (P.QA + P.β * pS + P.α * P.sA - η * P.sA + w + P.c + P.β * (P.r * pS + T - P.c))
      (-(w + P.c) * (P.QA + P.β * pS + P.α * P.sA - η * P.sA) +
        (P.r * pS + T - P.c) * (P.QS - pS + P.α * P.sA - η * P.sA)) pA one_pos
      (by intro x; simp only [profitAF, qAF, qSF]; ring)]
  rw [quad_argmax (fun x => profitSF P η T pA x) (1 - P.r)
      ((1 - P.r) * (P.QS + P.β * pA + P.α * P.sA - η * P.sA) + P.g + T)
      (-(P.g + T) * (P.QS + P.β * pA + P.α * P.sA - η * P.sA)) pS (by linarith)
      (by intro x; simp only [profitSF, qSF]; ring)]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩


lemma profitSN_eq (P : Params) (hr : P.r < 1) (η w pA pS : ℝ) (h : IsPriceNE_N P η w pA pS) :
    profitSN P η pA pS = (1 - P.r) * qSN P η pA pS ^ 2 := by
  obtain ⟨_, h2⟩ := (nashN_iff P hr η w pA pS).mp h
  have : (1 - P.r) * pS - P.g - P.c = (1 - P.r) * qSN P η pA pS := by
    unfold qSN; linarith
  unfold profitSN; rw [this]; ring

lemma profitSF_eq (P : Params) (hr : P.r < 1) (η T w pA pS : ℝ) (h : IsPriceNE_F P η T w pA pS) :
    profitSF P η T pA pS = (1 - P.r) * qSF P η pA pS ^ 2 := by
  obtain ⟨_, h2⟩ := (nashF_iff P hr η T w pA pS).mp h
  have : (1 - P.r) * pS - P.g - T = (1 - P.r) * qSF P η pA pS := by
    unfold qSF; linarith
  unfold profitSF; rw [this]; ring


lemma qS_gap (P : Params) (hP : P.Standing) (η T : ℝ) :
    qSF P η (pAF_star P η T) (pSF_star P η T) - qSN P η (pAN_star P η) (pSN_star P η) =
      (1 - P.β ^ 2) * (8 - (3 + P.r) * P.β ^ 2) /
        (2 * (1 - P.r) * (2 - P.β ^ 2) * (4 - (1 + P.r) * P.β ^ 2)) * (Tbar P η - T) := by
  obtain ⟨_, _, hb0, hb1, hr0, hr1, _⟩ := hP
  have h1 : (1 - P.r) ≠ 0 := by nlinarith
  have h2 : (4 - (1 + P.r) * P.β ^ 2) ≠ 0 := by nlinarith
  have h3 : (2 - P.β ^ 2) ≠ 0 := by nlinarith
  have h4 : (1 - P.β ^ 2) ≠ 0 := by nlinarith
  have h5 : (8 - (3 + P.r) * P.β ^ 2) ≠ 0 := by nlinarith
  simp only [qSF, qSN, pAN_star, pSN_star, pAF_star, pSF_star, Tbar]
  generalize hD : (4 - (1 + P.r) * P.β ^ 2) = D at h2 ⊢
  generalize hE : (2 - P.β ^ 2) = E at h3 ⊢
  generalize hF : (1 - P.β ^ 2) = F at h4 ⊢
  generalize hG : (8 - (3 + P.r) * P.β ^ 2) = G at h5 ⊢
  generalize hR : (1 - P.r) = R at h1 ⊢
  field_simp
  subst hD hE hF hG hR
  ring

end FBAComp.AmazonGain

open FBAComp.AmazonGain in
theorem solution (P : Params) (hP : P.Standing) (hI : Interior P)
    (η wN pAN pSN T wF pAF pSF : ℝ) (hη : η ∈ Set.Ioo 0 P.α)
    (hN : IsEqN P η wN pAN pSN) (hF : IsSubgameEqF P η T wF pAF pSF)
    (hSales : 0 ≤ qSF P η pAF pSF) :
    profitSN P η pAN pSN < profitSF P η T pAF pSF ↔ T < Tbar P η := by
  have hr : P.r < 1 := hP.2.2.2.2.2.1
  have hR : 0 < 1 - P.r := by linarith
  have hqN : 0 < qSN P η pAN pSN := hI η hη wN pAN pSN hN
  rw [profitSN_eq P hr η wN pAN pSN hN.1, profitSF_eq P hr η T wF pAF pSF hF.1]
  have hgap := qS_gap P hP η T
  obtain ⟨-, hA, hS⟩ := (lemma_A_1 P hP η wN pAN pSN).mp hN
  obtain ⟨-, hA', hS'⟩ := (lemma_A_2 P hP η T wF pAF pSF).mp hF
  rw [← hA, ← hS, ← hA', ← hS'] at hgap
  obtain ⟨_, _, hb0, hb1, hr0, hr1, _⟩ := hP
  have hm : 0 < (1 - P.β ^ 2) * (8 - (3 + P.r) * P.β ^ 2) /
      (2 * (1 - P.r) * (2 - P.β ^ 2) * (4 - (1 + P.r) * P.β ^ 2)) := by
    apply div_pos
    · apply mul_pos <;> nlinarith
    · apply mul_pos (mul_pos (by linarith) (by nlinarith)) (by nlinarith)
  constructor
  · intro h
    have h2 : qSN P η pAN pSN ^ 2 < qSF P η pAF pSF ^ 2 := lt_of_mul_lt_mul_left h hR.le
    have h3 : qSN P η pAN pSN < qSF P η pAF pSF := by nlinarith
    by_contra hc; push Not at hc
    nlinarith [mul_nonneg hm.le (sub_nonneg.mpr hc)]
  · intro h
    have h3 : qSN P η pAN pSN < qSF P η pAF pSF := by
      nlinarith [mul_pos hm (sub_pos.mpr h)]
    have h2 : qSN P η pAN pSN ^ 2 < qSF P η pAF pSF ^ 2 := by nlinarith
    exact mul_lt_mul_of_pos_left h2 hR
