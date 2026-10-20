-- Prove2me | solution 1 for FBAComp.AmazonGain.prop2_convexity_Tbar
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T04:02:56.932778+00:00
-- url     : https://prove2.me/submissions/73d565c1-118b-42a3-b680-cc68e8eb0256

import Mathlib
import Theorems.Thm_FBAComp_AmazonGain_lemma_A_1
import Theorems.Thm_FBAComp_AmazonGain_lemma_A_2

namespace FBAComp.AmazonGain


set_option maxHeartbeats 2000000 in
lemma bernA (b r : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    b^8*r + b^8 + b^7*r^2 + 3*b^7*r - 4*b^6*r - 7*b^6 - 3*b^5*r^2 - 20*b^5*r - 9*b^5 + 4*b^4*r + 14*b^4 + b^3*r^2 + 34*b^3*r + 45*b^3 - 4*b^2 - 8*b*r - 56*b - 8 + 8 ≤ 0 := by
  have hpos : ∀ u s : ℝ, 0 ≤ u → 0 ≤ s → 0 ≤ (56/1:ℝ) * b^1 * u^7 * r^0 * s^2 + (120/1:ℝ) * b^1 * u^7 * r^1 * s^1 + (64/1:ℝ) * b^1 * u^7 * r^2 * s^0 + (396/1:ℝ) * b^2 * u^6 * r^0 * s^2 + (848/1:ℝ) * b^2 * u^6 * r^1 * s^1 + (452/1:ℝ) * b^2 * u^6 * r^2 * s^0 + (1155/1:ℝ) * b^3 * u^5 * r^0 * s^2 + (2444/1:ℝ) * b^3 * u^5 * r^1 * s^1 + (1288/1:ℝ) * b^3 * u^5 * r^2 * s^0 + (1781/1:ℝ) * b^4 * u^4 * r^0 * s^2 + (3668/1:ℝ) * b^4 * u^4 * r^1 * s^1 + (1882/1:ℝ) * b^4 * u^4 * r^2 * s^0 + (1543/1:ℝ) * b^5 * u^3 * r^0 * s^2 + (3030/1:ℝ) * b^5 * u^3 * r^1 * s^1 + (1480/1:ℝ) * b^5 * u^3 * r^2 * s^0 + (736/1:ℝ) * b^6 * u^2 * r^0 * s^2 + (1340/1:ℝ) * b^6 * u^2 * r^1 * s^1 + (603/1:ℝ) * b^6 * u^2 * r^2 * s^0 + (176/1:ℝ) * b^7 * u^1 * r^0 * s^2 + (287/1:ℝ) * b^7 * u^1 * r^1 * s^1 + (114/1:ℝ) * b^7 * u^1 * r^2 * s^0 + (16/1:ℝ) * b^8 * u^0 * r^0 * s^2 + (22/1:ℝ) * b^8 * u^0 * r^1 * s^1 + (7/1:ℝ) * b^8 * u^0 * r^2 * s^0 := by
    intro u s hu hs; positivity
  have key : b^8*r + b^8 + b^7*r^2 + 3*b^7*r - 4*b^6*r - 7*b^6 - 3*b^5*r^2 - 20*b^5*r - 9*b^5 + 4*b^4*r + 14*b^4 + b^3*r^2 + 34*b^3*r + 45*b^3 - 4*b^2 - 8*b*r - 56*b - 8 + 8 = -((56/1:ℝ) * b^1 * (1-b)^7 * r^0 * (1-r)^2 + (120/1:ℝ) * b^1 * (1-b)^7 * r^1 * (1-r)^1 + (64/1:ℝ) * b^1 * (1-b)^7 * r^2 * (1-r)^0 + (396/1:ℝ) * b^2 * (1-b)^6 * r^0 * (1-r)^2 + (848/1:ℝ) * b^2 * (1-b)^6 * r^1 * (1-r)^1 + (452/1:ℝ) * b^2 * (1-b)^6 * r^2 * (1-r)^0 + (1155/1:ℝ) * b^3 * (1-b)^5 * r^0 * (1-r)^2 + (2444/1:ℝ) * b^3 * (1-b)^5 * r^1 * (1-r)^1 + (1288/1:ℝ) * b^3 * (1-b)^5 * r^2 * (1-r)^0 + (1781/1:ℝ) * b^4 * (1-b)^4 * r^0 * (1-r)^2 + (3668/1:ℝ) * b^4 * (1-b)^4 * r^1 * (1-r)^1 + (1882/1:ℝ) * b^4 * (1-b)^4 * r^2 * (1-r)^0 + (1543/1:ℝ) * b^5 * (1-b)^3 * r^0 * (1-r)^2 + (3030/1:ℝ) * b^5 * (1-b)^3 * r^1 * (1-r)^1 + (1480/1:ℝ) * b^5 * (1-b)^3 * r^2 * (1-r)^0 + (736/1:ℝ) * b^6 * (1-b)^2 * r^0 * (1-r)^2 + (1340/1:ℝ) * b^6 * (1-b)^2 * r^1 * (1-r)^1 + (603/1:ℝ) * b^6 * (1-b)^2 * r^2 * (1-r)^0 + (176/1:ℝ) * b^7 * (1-b)^1 * r^0 * (1-r)^2 + (287/1:ℝ) * b^7 * (1-b)^1 * r^1 * (1-r)^1 + (114/1:ℝ) * b^7 * (1-b)^1 * r^2 * (1-r)^0 + (16/1:ℝ) * b^8 * (1-b)^0 * r^0 * (1-r)^2 + (22/1:ℝ) * b^8 * (1-b)^0 * r^1 * (1-r)^1 + (7/1:ℝ) * b^8 * (1-b)^0 * r^2 * (1-r)^0) := by ring
  have := hpos (1 - b) (1 - r) (by linarith) (by linarith)
  linarith

set_option maxHeartbeats 2000000 in
lemma bernB (b r : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    b^8*r^2 + 2*b^8*r - b^8 - 3*b^6*r^2 - 15*b^6*r + b^6 + b^4*r^2 + 27*b^4*r + 14*b^4 - 6*b^2*r - 22*b^2 - 8 + 8 ≤ 0 := by
  have hpos : ∀ u s : ℝ, 0 ≤ u → 0 ≤ s → 0 ≤ (22/1:ℝ) * b^2 * u^6 * r^0 * s^2 + (50/1:ℝ) * b^2 * u^6 * r^1 * s^1 + (28/1:ℝ) * b^2 * u^6 * r^2 * s^0 + (132/1:ℝ) * b^3 * u^5 * r^0 * s^2 + (300/1:ℝ) * b^3 * u^5 * r^1 * s^1 + (168/1:ℝ) * b^3 * u^5 * r^2 * s^0 + (316/1:ℝ) * b^4 * u^4 * r^0 * s^2 + (695/1:ℝ) * b^4 * u^4 * r^1 * s^1 + (378/1:ℝ) * b^4 * u^4 * r^2 * s^0 + (384/1:ℝ) * b^5 * u^3 * r^0 * s^2 + (780/1:ℝ) * b^5 * u^3 * r^1 * s^1 + (392/1:ℝ) * b^5 * u^3 * r^2 * s^0 + (245/1:ℝ) * b^6 * u^2 * r^0 * s^2 + (433/1:ℝ) * b^6 * u^2 * r^1 * s^1 + (185/1:ℝ) * b^6 * u^2 * r^2 * s^0 + (74/1:ℝ) * b^7 * u^1 * r^0 * s^2 + (106/1:ℝ) * b^7 * u^1 * r^1 * s^1 + (34/1:ℝ) * b^7 * u^1 * r^2 * s^0 + (8/1:ℝ) * b^8 * u^0 * r^0 * s^2 + (8/1:ℝ) * b^8 * u^0 * r^1 * s^1 + (1/1:ℝ) * b^8 * u^0 * r^2 * s^0 := by
    intro u s hu hs; positivity
  have key : b^8*r^2 + 2*b^8*r - b^8 - 3*b^6*r^2 - 15*b^6*r + b^6 + b^4*r^2 + 27*b^4*r + 14*b^4 - 6*b^2*r - 22*b^2 - 8 + 8 = -((22/1:ℝ) * b^2 * (1-b)^6 * r^0 * (1-r)^2 + (50/1:ℝ) * b^2 * (1-b)^6 * r^1 * (1-r)^1 + (28/1:ℝ) * b^2 * (1-b)^6 * r^2 * (1-r)^0 + (132/1:ℝ) * b^3 * (1-b)^5 * r^0 * (1-r)^2 + (300/1:ℝ) * b^3 * (1-b)^5 * r^1 * (1-r)^1 + (168/1:ℝ) * b^3 * (1-b)^5 * r^2 * (1-r)^0 + (316/1:ℝ) * b^4 * (1-b)^4 * r^0 * (1-r)^2 + (695/1:ℝ) * b^4 * (1-b)^4 * r^1 * (1-r)^1 + (378/1:ℝ) * b^4 * (1-b)^4 * r^2 * (1-r)^0 + (384/1:ℝ) * b^5 * (1-b)^3 * r^0 * (1-r)^2 + (780/1:ℝ) * b^5 * (1-b)^3 * r^1 * (1-r)^1 + (392/1:ℝ) * b^5 * (1-b)^3 * r^2 * (1-r)^0 + (245/1:ℝ) * b^6 * (1-b)^2 * r^0 * (1-r)^2 + (433/1:ℝ) * b^6 * (1-b)^2 * r^1 * (1-r)^1 + (185/1:ℝ) * b^6 * (1-b)^2 * r^2 * (1-r)^0 + (74/1:ℝ) * b^7 * (1-b)^1 * r^0 * (1-r)^2 + (106/1:ℝ) * b^7 * (1-b)^1 * r^1 * (1-r)^1 + (34/1:ℝ) * b^7 * (1-b)^1 * r^2 * (1-r)^0 + (8/1:ℝ) * b^8 * (1-b)^0 * r^0 * (1-r)^2 + (8/1:ℝ) * b^8 * (1-b)^0 * r^1 * (1-r)^1 + (1/1:ℝ) * b^8 * (1-b)^0 * r^2 * (1-r)^0) := by ring
  have := hpos (1 - b) (1 - r) (by linarith) (by linarith)
  linarith

lemma aff_wNs (P : Params) (a b t : ℝ) :
    wN_star P ((1 - t) * a + t * b) = (1 - t) * (wN_star P a) + t * (wN_star P b) := by
  simp only [wN_star, pAN_star, pSN_star, wF_star, pAF_star, pSF_star, Tbar]; ring

lemma dif_wNs (P : Params) (a b : ℝ) :
    wN_star P a - wN_star P b = (a - b) * (wN_star P 1 - wN_star P 0) := by
  simp only [wN_star, pAN_star, pSN_star, wF_star, pAF_star, pSF_star, Tbar]; ring

lemma aff_pANs (P : Params) (a b t : ℝ) :
    pAN_star P ((1 - t) * a + t * b) = (1 - t) * (pAN_star P a) + t * (pAN_star P b) := by
  simp only [wN_star, pAN_star, pSN_star, wF_star, pAF_star, pSF_star, Tbar]; ring

lemma dif_pANs (P : Params) (a b : ℝ) :
    pAN_star P a - pAN_star P b = (a - b) * (pAN_star P 1 - pAN_star P 0) := by
  simp only [wN_star, pAN_star, pSN_star, wF_star, pAF_star, pSF_star, Tbar]; ring

lemma aff_pSNs (P : Params) (a b t : ℝ) :
    pSN_star P ((1 - t) * a + t * b) = (1 - t) * (pSN_star P a) + t * (pSN_star P b) := by
  simp only [wN_star, pAN_star, pSN_star, wF_star, pAF_star, pSF_star, Tbar]; ring

lemma dif_pSNs (P : Params) (a b : ℝ) :
    pSN_star P a - pSN_star P b = (a - b) * (pSN_star P 1 - pSN_star P 0) := by
  simp only [wN_star, pAN_star, pSN_star, wF_star, pAF_star, pSF_star, Tbar]; ring

lemma aff_Tbs (P : Params) (a b t : ℝ) :
    Tbar P ((1 - t) * a + t * b) = (1 - t) * (Tbar P a) + t * (Tbar P b) := by
  simp only [wN_star, pAN_star, pSN_star, wF_star, pAF_star, pSF_star, Tbar]; ring

lemma dif_Tbs (P : Params) (a b : ℝ) :
    Tbar P a - Tbar P b = (a - b) * (Tbar P 1 - Tbar P 0) := by
  simp only [wN_star, pAN_star, pSN_star, wF_star, pAF_star, pSF_star, Tbar]; ring

lemma aff_wFs (P : Params) (a b t : ℝ) :
    wF_star P ((1 - t) * a + t * b) (Tbar P ((1 - t) * a + t * b)) = (1 - t) * (wF_star P a (Tbar P a)) + t * (wF_star P b (Tbar P b)) := by
  simp only [wN_star, pAN_star, pSN_star, wF_star, pAF_star, pSF_star, Tbar]; ring

lemma dif_wFs (P : Params) (a b : ℝ) :
    wF_star P a (Tbar P a) - wF_star P b (Tbar P b) = (a - b) * (wF_star P 1 (Tbar P 1) - wF_star P 0 (Tbar P 0)) := by
  simp only [wN_star, pAN_star, pSN_star, wF_star, pAF_star, pSF_star, Tbar]; ring

lemma aff_pAFs (P : Params) (a b t : ℝ) :
    pAF_star P ((1 - t) * a + t * b) (Tbar P ((1 - t) * a + t * b)) = (1 - t) * (pAF_star P a (Tbar P a)) + t * (pAF_star P b (Tbar P b)) := by
  simp only [wN_star, pAN_star, pSN_star, wF_star, pAF_star, pSF_star, Tbar]; ring

lemma dif_pAFs (P : Params) (a b : ℝ) :
    pAF_star P a (Tbar P a) - pAF_star P b (Tbar P b) = (a - b) * (pAF_star P 1 (Tbar P 1) - pAF_star P 0 (Tbar P 0)) := by
  simp only [wN_star, pAN_star, pSN_star, wF_star, pAF_star, pSF_star, Tbar]; ring

lemma aff_pSFs (P : Params) (a b t : ℝ) :
    pSF_star P ((1 - t) * a + t * b) (Tbar P ((1 - t) * a + t * b)) = (1 - t) * (pSF_star P a (Tbar P a)) + t * (pSF_star P b (Tbar P b)) := by
  simp only [wN_star, pAN_star, pSN_star, wF_star, pAF_star, pSF_star, Tbar]; ring

lemma dif_pSFs (P : Params) (a b : ℝ) :
    pSF_star P a (Tbar P a) - pSF_star P b (Tbar P b) = (a - b) * (pSF_star P 1 (Tbar P 1) - pSF_star P 0 (Tbar P 0)) := by
  simp only [wN_star, pAN_star, pSN_star, wF_star, pAF_star, pSF_star, Tbar]; ring

def Q2 (P : Params) (dη dwN dpAN dpSN dT dwF dpAF dpSF : ℝ) : ℝ :=
  ((dpAF - dwF) * (-dpAF + P.β * dpSF - dη * P.sA) + (P.r * dpSF + dT) * (-dpSF + P.β * dpAF - dη * P.sA)) -
  ((dpAN - dwN) * (-dpAN + P.β * dpSN - dη * P.sS) + P.r * dpSN * (-dpSN + P.β * dpAN - dη * P.sA))

lemma gain_cvx_id (P : Params) (η1 wN1 pAN1 pSN1 T1 wF1 pAF1 pSF1 η2 wN2 pAN2 pSN2 T2 wF2 pAF2 pSF2 t : ℝ) :
    (1 - t) * gain P η1 wN1 pAN1 pSN1 T1 wF1 pAF1 pSF1 + t * gain P η2 wN2 pAN2 pSN2 T2 wF2 pAF2 pSF2 -
      gain P ((1 - t) * η1 + t * η2) ((1 - t) * wN1 + t * wN2) ((1 - t) * pAN1 + t * pAN2)
        ((1 - t) * pSN1 + t * pSN2) ((1 - t) * T1 + t * T2) ((1 - t) * wF1 + t * wF2)
        ((1 - t) * pAF1 + t * pAF2) ((1 - t) * pSF1 + t * pSF2) =
    t * (1 - t) * Q2 P (η1 - η2) (wN1 - wN2) (pAN1 - pAN2) (pSN1 - pSN2) (T1 - T2) (wF1 - wF2)
      (pAF1 - pAF2) (pSF1 - pSF2) := by
  simp only [gain, profitAF, profitAN, qAF, qSF, qAN, qSN, Q2]; ring

lemma Q2_hom (P : Params) (k a2 a3 a4 a5 a6 a7 a8 : ℝ) :
    Q2 P k (k * a2) (k * a3) (k * a4) (k * a5) (k * a6) (k * a7) (k * a8) =
      k ^ 2 * Q2 P 1 a2 a3 a4 a5 a6 a7 a8 := by
  simp only [Q2]; ring

set_option maxHeartbeats 4000000 in
lemma Q2_val (P : Params) (hP : P.Standing) :
    Q2 P 1 (wN_star P 1 - wN_star P 0) (pAN_star P 1 - pAN_star P 0) (pSN_star P 1 - pSN_star P 0) (Tbar P 1 - Tbar P 0) (wF_star P 1 (Tbar P 1) - wF_star P 0 (Tbar P 0)) (pAF_star P 1 (Tbar P 1) - pAF_star P 0 (Tbar P 0)) (pSF_star P 1 (Tbar P 1) - pSF_star P 0 (Tbar P 0)) =
      -(P.sA - P.sS) * (P.β^8*P.r^2*P.sS + P.β^8*P.r*P.sA + 2*P.β^8*P.r*P.sS + P.β^8*P.sA - P.β^8*P.sS + P.β^7*P.r^2*P.sA + 3*P.β^7*P.r*P.sA - 3*P.β^6*P.r^2*P.sS - 4*P.β^6*P.r*P.sA - 15*P.β^6*P.r*P.sS - 7*P.β^6*P.sA + P.β^6*P.sS - 3*P.β^5*P.r^2*P.sA - 20*P.β^5*P.r*P.sA - 9*P.β^5*P.sA + P.β^4*P.r^2*P.sS + 4*P.β^4*P.r*P.sA + 27*P.β^4*P.r*P.sS + 14*P.β^4*P.sA + 14*P.β^4*P.sS + P.β^3*P.r^2*P.sA + 34*P.β^3*P.r*P.sA + 45*P.β^3*P.sA - 6*P.β^2*P.r*P.sS - 4*P.β^2*P.sA - 22*P.β^2*P.sS - 8*P.β*P.r*P.sA - 56*P.β*P.sA - 8*P.sA - 8*P.sS) /
        ((1 - P.β ^ 2) * (2 - P.β ^ 2) * (8 - (3 + P.r) * P.β ^ 2) ^ 2) := by
  obtain ⟨_, _, hb0, hb1, hr0, hr1, _⟩ := hP
  have h1 : (1 - P.r) ≠ 0 := by nlinarith
  have h2 : (4 - (1 + P.r) * P.β ^ 2) ≠ 0 := by nlinarith
  have h3 : (2 - P.β ^ 2) ≠ 0 := by nlinarith
  have h4 : (1 - P.β ^ 2) ≠ 0 := by nlinarith
  have h5 : (8 - (3 + P.r) * P.β ^ 2) ≠ 0 := by nlinarith
  simp only [Q2, wN_star, pAN_star, pSN_star, wF_star, pAF_star, pSF_star, Tbar]
  generalize hD : (4 - (1 + P.r) * P.β ^ 2) = D at h2 ⊢
  generalize hE : (2 - P.β ^ 2) = E at h3 ⊢
  generalize hF : (1 - P.β ^ 2) = F at h4 ⊢
  generalize hG : (8 - (3 + P.r) * P.β ^ 2) = G at h5 ⊢
  generalize hR : (1 - P.r) = R at h1 ⊢
  field_simp
  subst hD hE hF hG hR
  ring

lemma Q2_nonneg (P : Params) (hP : P.Standing) : 0 ≤ Q2 P 1 (wN_star P 1 - wN_star P 0) (pAN_star P 1 - pAN_star P 0) (pSN_star P 1 - pSN_star P 0) (Tbar P 1 - Tbar P 0) (wF_star P 1 (Tbar P 1) - wF_star P 0 (Tbar P 0)) (pAF_star P 1 (Tbar P 1) - pAF_star P 0 (Tbar P 0)) (pSF_star P 1 (Tbar P 1) - pSF_star P 0 (Tbar P 0)) := by
  rw [Q2_val P hP]
  obtain ⟨_, _, hb0, hb1, hr0, hr1, hs0, hs1, _⟩ := hP
  have hA := bernA P.β P.r hb0.le hb1.le hr0.le hr1.le
  have hB := bernB P.β P.r hb0.le hb1.le hr0.le hr1.le
  have hW : P.β^8*P.r^2*P.sS + P.β^8*P.r*P.sA + 2*P.β^8*P.r*P.sS + P.β^8*P.sA - P.β^8*P.sS + P.β^7*P.r^2*P.sA + 3*P.β^7*P.r*P.sA - 3*P.β^6*P.r^2*P.sS - 4*P.β^6*P.r*P.sA - 15*P.β^6*P.r*P.sS - 7*P.β^6*P.sA + P.β^6*P.sS - 3*P.β^5*P.r^2*P.sA - 20*P.β^5*P.r*P.sA - 9*P.β^5*P.sA + P.β^4*P.r^2*P.sS + 4*P.β^4*P.r*P.sA + 27*P.β^4*P.r*P.sS + 14*P.β^4*P.sA + 14*P.β^4*P.sS + P.β^3*P.r^2*P.sA + 34*P.β^3*P.r*P.sA + 45*P.β^3*P.sA - 6*P.β^2*P.r*P.sS - 4*P.β^2*P.sA - 22*P.β^2*P.sS - 8*P.β*P.r*P.sA - 56*P.β*P.sA - 8*P.sA - 8*P.sS < 0 := by nlinarith
  apply div_nonneg
  · nlinarith
  · have : 0 < 1 - P.β ^ 2 := by nlinarith
    have : 0 < 2 - P.β ^ 2 := by nlinarith
    positivity

end FBAComp.AmazonGain

open FBAComp.AmazonGain in
theorem solution (P : Params) (hP : P.Standing) :
    ∀ η₁ η₂ : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ ηm : ℝ,
      ηm = (1 - t) * η₁ + t * η₂ →
      ∀ wN₁ pAN₁ pSN₁ wF₁ pAF₁ pSF₁ : ℝ,
      ∀ wN₂ pAN₂ pSN₂ wF₂ pAF₂ pSF₂ : ℝ,
      ∀ wNm pANm pSNm wFm pAFm pSFm : ℝ,
        IsEqN P η₁ wN₁ pAN₁ pSN₁ →
        IsSubgameEqF P η₁ (Tbar P η₁) wF₁ pAF₁ pSF₁ →
        IsEqN P η₂ wN₂ pAN₂ pSN₂ →
        IsSubgameEqF P η₂ (Tbar P η₂) wF₂ pAF₂ pSF₂ →
        IsEqN P ηm wNm pANm pSNm →
        IsSubgameEqF P ηm (Tbar P ηm) wFm pAFm pSFm →
        gain P ηm wNm pANm pSNm (Tbar P ηm) wFm pAFm pSFm ≤
          (1 - t) * gain P η₁ wN₁ pAN₁ pSN₁ (Tbar P η₁) wF₁ pAF₁ pSF₁ +
            t * gain P η₂ wN₂ pAN₂ pSN₂ (Tbar P η₂) wF₂ pAF₂ pSF₂ := by
  intro η₁ η₂ t ht ηm hm wN₁ pAN₁ pSN₁ wF₁ pAF₁ pSF₁ wN₂ pAN₂ pSN₂ wF₂ pAF₂ pSF₂
    wNm pANm pSNm wFm pAFm pSFm h1 h1' h2 h2' h3 h3'
  obtain ⟨rfl, rfl, rfl⟩ := (lemma_A_1 P hP _ _ _ _).mp h1
  obtain ⟨rfl, rfl, rfl⟩ := (lemma_A_2 P hP _ _ _ _ _).mp h1'
  obtain ⟨rfl, rfl, rfl⟩ := (lemma_A_1 P hP _ _ _ _).mp h2
  obtain ⟨rfl, rfl, rfl⟩ := (lemma_A_2 P hP _ _ _ _ _).mp h2'
  obtain ⟨rfl, rfl, rfl⟩ := (lemma_A_1 P hP _ _ _ _).mp h3
  obtain ⟨rfl, rfl, rfl⟩ := (lemma_A_2 P hP _ _ _ _ _).mp h3'
  subst hm
  have hid := gain_cvx_id P η₁ (wN_star P η₁) (pAN_star P η₁) (pSN_star P η₁) (Tbar P η₁)
    (wF_star P η₁ (Tbar P η₁)) (pAF_star P η₁ (Tbar P η₁)) (pSF_star P η₁ (Tbar P η₁))
    η₂ (wN_star P η₂) (pAN_star P η₂) (pSN_star P η₂) (Tbar P η₂)
    (wF_star P η₂ (Tbar P η₂)) (pAF_star P η₂ (Tbar P η₂)) (pSF_star P η₂ (Tbar P η₂)) t
  rw [← aff_wNs, ← aff_pANs, ← aff_pSNs, ← aff_Tbs, ← aff_wFs, ← aff_pAFs, ← aff_pSFs,
    dif_wNs, dif_pANs, dif_pSNs, dif_Tbs, dif_wFs, dif_pAFs, dif_pSFs,
    Q2_hom] at hid
  have hQ := Q2_nonneg P hP
  have ht0 : 0 ≤ t * (1 - t) := mul_nonneg ht.1 (by linarith [ht.2])
  have : 0 ≤ t * (1 - t) * ((η₁ - η₂) ^ 2 * Q2 P 1 (wN_star P 1 - wN_star P 0) (pAN_star P 1 - pAN_star P 0) (pSN_star P 1 - pSN_star P 0) (Tbar P 1 - Tbar P 0) (wF_star P 1 (Tbar P 1) - wF_star P 0 (Tbar P 0)) (pAF_star P 1 (Tbar P 1) - pAF_star P 0 (Tbar P 0)) (pSF_star P 1 (Tbar P 1) - pSF_star P 0 (Tbar P 0))) :=
    mul_nonneg ht0 (mul_nonneg (sq_nonneg _) hQ)
  linarith
