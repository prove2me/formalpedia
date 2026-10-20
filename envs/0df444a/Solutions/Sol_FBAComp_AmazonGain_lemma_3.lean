-- Prove2me | solution 1 for FBAComp.AmazonGain.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T03:52:19.85978+00:00
-- url     : https://prove2.me/submissions/def959fd-2532-4a17-b9bd-bc63eebecb45

import Mathlib
import Definitions.Def_FBAComp_AmazonGain_Model

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

end FBAComp.AmazonGain

open FBAComp.AmazonGain in
theorem solution (P : Params) (hP : P.Standing)
    (η wN pAN pSN T wF pAF pSF : ℝ) (hη : η ∈ Set.Ioo 0 P.α)
    (hN : IsEqN P η wN pAN pSN)
    (hF : IsFeeOptimal P η (profitSN P η pAN pSN) T wF pAF pSF) :
    qSN P η pAN pSN ≤ qSF P η pAF pSF := by
  have hr : P.r < 1 := hP.2.2.2.2.2.1
  have hr' : 0 < 1 - P.r := by linarith
  obtain ⟨hsub, hpart, hq, _⟩ := hF
  rw [profitSN_eq P hr η wN pAN pSN hN.1, profitSF_eq P hr η T wF pAF pSF hsub.1] at hpart
  have h2 : qSN P η pAN pSN ^ 2 ≤ qSF P η pAF pSF ^ 2 := le_of_mul_le_mul_left hpart hr'
  exact (abs_le_of_sq_le_sq' h2 hq).2
