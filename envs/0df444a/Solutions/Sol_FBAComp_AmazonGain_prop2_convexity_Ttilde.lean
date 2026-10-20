-- Prove2me | solution 1 for FBAComp.AmazonGain.prop2_convexity_Ttilde
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T04:40:39.3777+00:00
-- url     : https://prove2.me/submissions/3e65bb32-401e-4a6a-af18-52379fdebcce

import Mathlib
import Theorems.Thm_FBAComp_AmazonGain_lemma_A_1
import Theorems.Thm_FBAComp_AmazonGain_lemma_A_2
import Theorems.Thm_FBAComp_AmazonGain_prop2_convexity_Tbar

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


set_option maxHeartbeats 4000000 in
lemma bern_p8 (b r : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    b^8*r^3 - b^8*r^2 - b^8*r + b^8 - 4*b^6*r^3 - 5*b^6*r^2 + 14*b^6*r - 5*b^6 + 3*b^4*r^3 + 30*b^4*r^2 - 29*b^4*r - 20*b^4 - 28*b^2*r^2 - 24*b^2*r + 116*b^2 + 64*r - 128 + 16 ≤ 0 := by
  have hpos : ∀ u s : ℝ, 0 ≤ u → 0 ≤ s → 0 ≤ (112/1:ℝ) * b^0 * u^8 * r^0 * s^3 + (272/1:ℝ) * b^0 * u^8 * r^1 * s^2 + (208/1:ℝ) * b^0 * u^8 * r^2 * s^1 + (48/1:ℝ) * b^0 * u^8 * r^3 * s^0 + (896/1:ℝ) * b^1 * u^7 * r^0 * s^3 + (2176/1:ℝ) * b^1 * u^7 * r^1 * s^2 + (1664/1:ℝ) * b^1 * u^7 * r^2 * s^1 + (384/1:ℝ) * b^1 * u^7 * r^3 * s^0 + (3020/1:ℝ) * b^2 * u^6 * r^0 * s^3 + (7292/1:ℝ) * b^2 * u^6 * r^1 * s^2 + (5552/1:ℝ) * b^2 * u^6 * r^2 * s^1 + (1280/1:ℝ) * b^2 * u^6 * r^3 * s^0 + (5576/1:ℝ) * b^3 * u^5 * r^0 * s^3 + (13288/1:ℝ) * b^3 * u^5 * r^1 * s^2 + (10016/1:ℝ) * b^3 * u^5 * r^2 * s^1 + (2304/1:ℝ) * b^3 * u^5 * r^3 * s^0 + (6120/1:ℝ) * b^4 * u^4 * r^0 * s^3 + (14269/1:ℝ) * b^4 * u^4 * r^1 * s^2 + (10568/1:ℝ) * b^4 * u^4 * r^2 * s^1 + (2416/1:ℝ) * b^4 * u^4 * r^3 * s^0 + (4032/1:ℝ) * b^5 * u^3 * r^0 * s^3 + (9108/1:ℝ) * b^5 * u^3 * r^1 * s^2 + (6560/1:ℝ) * b^5 * u^3 * r^2 * s^1 + (1472/1:ℝ) * b^5 * u^3 * r^3 * s^0 + (1521/1:ℝ) * b^6 * u^2 * r^0 * s^3 + (3291/1:ℝ) * b^6 * u^2 * r^1 * s^2 + (2264/1:ℝ) * b^6 * u^2 * r^2 * s^1 + (480/1:ℝ) * b^6 * u^2 * r^3 * s^0 + (290/1:ℝ) * b^7 * u^1 * r^0 * s^3 + (590/1:ℝ) * b^7 * u^1 * r^1 * s^2 + (368/1:ℝ) * b^7 * u^1 * r^2 * s^1 + (64/1:ℝ) * b^7 * u^1 * r^3 * s^0 + (20/1:ℝ) * b^8 * u^0 * r^0 * s^3 + (36/1:ℝ) * b^8 * u^0 * r^1 * s^2 + (16/1:ℝ) * b^8 * u^0 * r^2 * s^1 := by
    intro u s hu hs; positivity
  have key : b^8*r^3 - b^8*r^2 - b^8*r + b^8 - 4*b^6*r^3 - 5*b^6*r^2 + 14*b^6*r - 5*b^6 + 3*b^4*r^3 + 30*b^4*r^2 - 29*b^4*r - 20*b^4 - 28*b^2*r^2 - 24*b^2*r + 116*b^2 + 64*r - 128 + 16 = -((112/1:ℝ) * b^0 * (1-b)^8 * r^0 * (1-r)^3 + (272/1:ℝ) * b^0 * (1-b)^8 * r^1 * (1-r)^2 + (208/1:ℝ) * b^0 * (1-b)^8 * r^2 * (1-r)^1 + (48/1:ℝ) * b^0 * (1-b)^8 * r^3 * (1-r)^0 + (896/1:ℝ) * b^1 * (1-b)^7 * r^0 * (1-r)^3 + (2176/1:ℝ) * b^1 * (1-b)^7 * r^1 * (1-r)^2 + (1664/1:ℝ) * b^1 * (1-b)^7 * r^2 * (1-r)^1 + (384/1:ℝ) * b^1 * (1-b)^7 * r^3 * (1-r)^0 + (3020/1:ℝ) * b^2 * (1-b)^6 * r^0 * (1-r)^3 + (7292/1:ℝ) * b^2 * (1-b)^6 * r^1 * (1-r)^2 + (5552/1:ℝ) * b^2 * (1-b)^6 * r^2 * (1-r)^1 + (1280/1:ℝ) * b^2 * (1-b)^6 * r^3 * (1-r)^0 + (5576/1:ℝ) * b^3 * (1-b)^5 * r^0 * (1-r)^3 + (13288/1:ℝ) * b^3 * (1-b)^5 * r^1 * (1-r)^2 + (10016/1:ℝ) * b^3 * (1-b)^5 * r^2 * (1-r)^1 + (2304/1:ℝ) * b^3 * (1-b)^5 * r^3 * (1-r)^0 + (6120/1:ℝ) * b^4 * (1-b)^4 * r^0 * (1-r)^3 + (14269/1:ℝ) * b^4 * (1-b)^4 * r^1 * (1-r)^2 + (10568/1:ℝ) * b^4 * (1-b)^4 * r^2 * (1-r)^1 + (2416/1:ℝ) * b^4 * (1-b)^4 * r^3 * (1-r)^0 + (4032/1:ℝ) * b^5 * (1-b)^3 * r^0 * (1-r)^3 + (9108/1:ℝ) * b^5 * (1-b)^3 * r^1 * (1-r)^2 + (6560/1:ℝ) * b^5 * (1-b)^3 * r^2 * (1-r)^1 + (1472/1:ℝ) * b^5 * (1-b)^3 * r^3 * (1-r)^0 + (1521/1:ℝ) * b^6 * (1-b)^2 * r^0 * (1-r)^3 + (3291/1:ℝ) * b^6 * (1-b)^2 * r^1 * (1-r)^2 + (2264/1:ℝ) * b^6 * (1-b)^2 * r^2 * (1-r)^1 + (480/1:ℝ) * b^6 * (1-b)^2 * r^3 * (1-r)^0 + (290/1:ℝ) * b^7 * (1-b)^1 * r^0 * (1-r)^3 + (590/1:ℝ) * b^7 * (1-b)^1 * r^1 * (1-r)^2 + (368/1:ℝ) * b^7 * (1-b)^1 * r^2 * (1-r)^1 + (64/1:ℝ) * b^7 * (1-b)^1 * r^3 * (1-r)^0 + (20/1:ℝ) * b^8 * (1-b)^0 * r^0 * (1-r)^3 + (36/1:ℝ) * b^8 * (1-b)^0 * r^1 * (1-r)^2 + (16/1:ℝ) * b^8 * (1-b)^0 * r^2 * (1-r)^1) := by ring
  have := hpos (1 - b) (1 - r) (by linarith) (by linarith)
  linarith

/-- Quadratic part of Amazon's FBA profit in the variables `(T, w, pA, pS)`. -/
def QF (P : Params) (dT dw dpA dpS : ℝ) : ℝ :=
  (dpA - dw) * (-dpA + P.β * dpS) + (P.r * dpS + dT) * (-dpS + P.β * dpA)

lemma profitAF_line (P : Params) (η T0 w0 pA0 pS0 dT dw dpA dpS s : ℝ) :
    profitAF P η (T0 + s * dT) (w0 + s * dw) (pA0 + s * dpA) (pS0 + s * dpS) =
      profitAF P η T0 w0 pA0 pS0 +
        s * (profitAF P η (T0 + dT) (w0 + dw) (pA0 + dpA) (pS0 + dpS) - profitAF P η T0 w0 pA0 pS0 -
          QF P dT dw dpA dpS) + s ^ 2 * QF P dT dw dpA dpS := by
  simp only [profitAF, qAF, qSF, QF]; ring

lemma affT_w (P : Params) (η T : ℝ) : wF_star P η T = wF_star P η 0 + T * (wF_star P η 1 - wF_star P η 0) := by
  simp only [wF_star]; ring
lemma affT_pA (P : Params) (η T : ℝ) : pAF_star P η T = pAF_star P η 0 + T * (pAF_star P η 1 - pAF_star P η 0) := by
  simp only [pAF_star]; ring
lemma affT_pS (P : Params) (η T : ℝ) : pSF_star P η T = pSF_star P η 0 + T * (pSF_star P η 1 - pSF_star P η 0) := by
  simp only [pSF_star]; ring

/-- Amazon's FBA profit along the subgame outcome, as a function of the fee. -/
noncomputable def phi (P : Params) (η T : ℝ) : ℝ :=
  profitAF P η T (wF_star P η T) (pAF_star P η T) (pSF_star P η T)

noncomputable def aF (P : Params) (η : ℝ) : ℝ :=
  QF P 1 (wF_star P η 1 - wF_star P η 0) (pAF_star P η 1 - pAF_star P η 0) (pSF_star P η 1 - pSF_star P η 0)

lemma phi_quad (P : Params) (η T : ℝ) :
    phi P η T = phi P η 0 + T * (phi P η 1 - phi P η 0 - aF P η) + T ^ 2 * aF P η := by
  have h := profitAF_line P η 0 (wF_star P η 0) (pAF_star P η 0) (pSF_star P η 0) 1
    (wF_star P η 1 - wF_star P η 0) (pAF_star P η 1 - pAF_star P η 0) (pSF_star P η 1 - pSF_star P η 0) T
  have e1 : wF_star P η 0 + (wF_star P η 1 - wF_star P η 0) = wF_star P η 1 := by ring
  have e2 : pAF_star P η 0 + (pAF_star P η 1 - pAF_star P η 0) = pAF_star P η 1 := by ring
  have e3 : pSF_star P η 0 + (pSF_star P η 1 - pSF_star P η 0) = pSF_star P η 1 := by ring
  rw [e1, e2, e3, ← affT_w, ← affT_pA, ← affT_pS, zero_add, mul_one, zero_add] at h
  unfold phi aF
  rw [h]

set_option maxHeartbeats 4000000 in
lemma aF_val (P : Params) (hP : P.Standing) (η : ℝ) :
    aF P η = (1 - P.β ^ 2) * (P.β^8*P.r^3 - P.β^8*P.r^2 - P.β^8*P.r + P.β^8 - 4*P.β^6*P.r^3 - 5*P.β^6*P.r^2 + 14*P.β^6*P.r - 5*P.β^6 + 3*P.β^4*P.r^3 + 30*P.β^4*P.r^2 - 29*P.β^4*P.r - 20*P.β^4 - 28*P.β^2*P.r^2 - 24*P.β^2*P.r + 116*P.β^2 + 64*P.r - 128) /
      (4 * (2 - P.β ^ 2) ^ 2 * (1 - P.r) ^ 2 * (4 - (1 + P.r) * P.β ^ 2) ^ 2) := by
  obtain ⟨_, _, hb0, hb1, hr0, hr1, _⟩ := hP
  have h1 : (1 - P.r) ≠ 0 := by nlinarith
  have h2 : (4 - (1 + P.r) * P.β ^ 2) ≠ 0 := by nlinarith
  have h3 : (2 - P.β ^ 2) ≠ 0 := by nlinarith
  simp only [aF, QF, wF_star, pAF_star, pSF_star]
  generalize hD : (4 - (1 + P.r) * P.β ^ 2) = D at h2 ⊢
  generalize hE : (2 - P.β ^ 2) = E at h3 ⊢
  generalize hR : (1 - P.r) = R at h1 ⊢
  field_simp
  subst hD hE hR
  ring

lemma aF_neg (P : Params) (hP : P.Standing) (η : ℝ) : aF P η < 0 := by
  rw [aF_val P hP η]
  obtain ⟨_, _, hb0, hb1, hr0, hr1, _⟩ := hP
  have hp := bern_p8 P.β P.r hb0.le hb1.le hr0.le hr1.le
  apply div_neg_of_neg_of_pos
  · apply mul_neg_of_pos_of_neg (by nlinarith) (by linarith)
  · have : 0 < 2 - P.β ^ 2 := by nlinarith
    have : 0 < 1 - P.r := by linarith
    have : 0 < 4 - (1 + P.r) * P.β ^ 2 := by nlinarith
    positivity


lemma vtx_global (f : ℝ → ℝ) (k b a T : ℝ) (ha : a < 0) (hf : ∀ x, f x = k + x * b + x ^ 2 * a) :
    (∀ x, f x ≤ f T) ↔ T = -b / (2 * a) := by
  have ha0 : a ≠ 0 := ha.ne
  have hdiff : ∀ x y, f x - f y = a * (x - y) * (x + y + b / a) := by
    intro x y; rw [hf, hf]; field_simp; ring
  constructor
  · intro h
    have h1 := h (-b / (2 * a))
    have h2 := hdiff (-b / (2 * a)) T
    have e : -b / (2 * a) + T + b / a = T - (-b / (2 * a)) := by field_simp; ring
    rw [e] at h2
    have : a * (T - -b / (2 * a)) ^ 2 ≥ 0 := by nlinarith
    have h3 : (T - -b / (2 * a)) ^ 2 ≤ 0 := by
      by_contra hc; push Not at hc; nlinarith [mul_neg_of_neg_of_pos ha hc]
    nlinarith [sq_nonneg (T - -b / (2 * a))]
  · rintro rfl x
    have h2 := hdiff x (-b / (2 * a))
    have e : x + -b / (2 * a) + b / a = x - (-b / (2 * a)) := by field_simp; ring
    rw [e] at h2
    nlinarith [mul_nonpos_of_nonpos_of_nonneg ha.le (sq_nonneg (x - -b / (2 * a)))]

lemma vtx_constr (f : ℝ → ℝ) (k b a T M : ℝ) (ha : a < 0) (hf : ∀ x, f x = k + x * b + x ^ 2 * a) :
    (T ≤ M ∧ ∀ x ≤ M, f x ≤ f T) ↔ T = min (-b / (2 * a)) M := by
  have ha0 : a ≠ 0 := ha.ne
  set v := -b / (2 * a) with hv
  have hdiff : ∀ x y, f x - f y = a * (x - y) * (x + y - 2 * v) := by
    intro x y; rw [hf, hf, hv]; field_simp; ring
  constructor
  · rintro ⟨hTM, h⟩
    rcases le_or_gt v M with hvM | hvM
    · rw [min_eq_left hvM]
      have h1 := h v hvM
      have h2 := hdiff v T
      have h3 : a * (T - v) ^ 2 ≥ 0 := by nlinarith
      have h4 : (T - v) ^ 2 ≤ 0 := by
        by_contra hc; push Not at hc; nlinarith [mul_neg_of_neg_of_pos ha hc]
      nlinarith [sq_nonneg (T - v)]
    · rw [min_eq_right hvM.le]
      have h1 := h M le_rfl
      have h2 := hdiff M T
      have h5 : 0 ≤ (M - T) * (2 * v - M - T) := mul_nonneg (by linarith) (by linarith)
      have h6 : (M - T) * (2 * v - M - T) ≤ 0 := by nlinarith
      have h7 : (M - T) * (2 * v - M - T) = 0 := le_antisymm h6 h5
      rcases mul_eq_zero.mp h7 with h | h <;> linarith
  · intro hT
    rcases le_or_gt v M with hvM | hvM
    · rw [min_eq_left hvM] at hT
      subst hT
      refine ⟨hvM, fun x _ => ?_⟩
      have h2 := hdiff x v
      nlinarith [mul_nonpos_of_nonpos_of_nonneg ha.le (sq_nonneg (x - v))]
    · rw [min_eq_right hvM.le] at hT
      subst hT
      refine ⟨le_rfl, fun x hx => ?_⟩
      have h2 := hdiff x T
      have h5 : 0 ≤ (T - x) * (2 * v - x - T) := mul_nonneg (by linarith) (by linarith)
      nlinarith [mul_nonpos_of_nonpos_of_nonneg ha.le h5]

/-- Feasibility of a fee in problem (5) is exactly `T ≤ T̄`. -/
lemma feasible_iff (P : Params) (hP : P.Standing) (η wN pAN pSN T : ℝ)
    (hN : IsEqN P η wN pAN pSN) (hq : 0 < qSN P η pAN pSN) :
    (profitSN P η pAN pSN ≤ profitSF P η T (pAF_star P η T) (pSF_star P η T) ∧
      0 ≤ qSF P η (pAF_star P η T) (pSF_star P η T)) ↔ T ≤ Tbar P η := by
  have hr : P.r < 1 := hP.2.2.2.2.2.1
  have hR : 0 < 1 - P.r := by linarith
  have hsub : IsSubgameEqF P η T (wF_star P η T) (pAF_star P η T) (pSF_star P η T) :=
    (lemma_A_2 P hP η T _ _ _).mpr ⟨rfl, rfl, rfl⟩
  rw [profitSN_eq P hr η wN pAN pSN hN.1, profitSF_eq P hr η T _ _ _ hsub.1]
  obtain ⟨-, hA, hS⟩ := (lemma_A_1 P hP η wN pAN pSN).mp hN
  have hgap := qS_gap P hP η T
  rw [← hA, ← hS] at hgap
  obtain ⟨_, _, hb0, hb1, hr0, hr1, _⟩ := hP
  have hm : 0 < (1 - P.β ^ 2) * (8 - (3 + P.r) * P.β ^ 2) /
      (2 * (1 - P.r) * (2 - P.β ^ 2) * (4 - (1 + P.r) * P.β ^ 2)) := by
    apply div_pos
    · apply mul_pos <;> nlinarith
    · apply mul_pos (mul_pos (by linarith) (by nlinarith)) (by nlinarith)
  constructor
  · rintro ⟨h1, h2⟩
    have h3 : qSN P η pAN pSN ^ 2 ≤ qSF P η (pAF_star P η T) (pSF_star P η T) ^ 2 :=
      le_of_mul_le_mul_left h1 hR
    have h4 := (abs_le_of_sq_le_sq' h3 h2).2
    by_contra hc; push Not at hc
    nlinarith [mul_pos hm (sub_pos.mpr hc)]
  · intro h
    have h3 : qSN P η pAN pSN ≤ qSF P η (pAF_star P η T) (pSF_star P η T) := by
      nlinarith [mul_nonneg hm.le (sub_nonneg.mpr h)]
    refine ⟨?_, by linarith⟩
    exact mul_le_mul_of_nonneg_left (by nlinarith) hR.le

lemma feeOpt_iff (P : Params) (hP : P.Standing) (η wN pAN pSN : ℝ)
    (hN : IsEqN P η wN pAN pSN) (hq : 0 < qSN P η pAN pSN) (T w pA pS : ℝ) :
    IsFeeOptimal P η (profitSN P η pAN pSN) T w pA pS ↔
      (w = wF_star P η T ∧ pA = pAF_star P η T ∧ pS = pSF_star P η T) ∧
        (T ≤ Tbar P η ∧ ∀ x ≤ Tbar P η, phi P η x ≤ phi P η T) := by
  constructor
  · rintro ⟨hsub, hpart, hsales, hopt⟩
    obtain ⟨rfl, rfl, rfl⟩ := (lemma_A_2 P hP η T w pA pS).mp hsub
    refine ⟨⟨rfl, rfl, rfl⟩, (feasible_iff P hP η wN pAN pSN T hN hq).mp ⟨hpart, hsales⟩, ?_⟩
    intro x hx
    obtain ⟨h1, h2⟩ := (feasible_iff P hP η wN pAN pSN x hN hq).mpr hx
    exact hopt x _ _ _ ((lemma_A_2 P hP η x _ _ _).mpr ⟨rfl, rfl, rfl⟩) h1 h2
  · rintro ⟨⟨rfl, rfl, rfl⟩, hTM, hopt⟩
    obtain ⟨h1, h2⟩ := (feasible_iff P hP η wN pAN pSN T hN hq).mpr hTM
    refine ⟨(lemma_A_2 P hP η T _ _ _).mpr ⟨rfl, rfl, rfl⟩, h1, h2, ?_⟩
    intro T' w' pA' pS' hsub' hp' hs'
    obtain ⟨rfl, rfl, rfl⟩ := (lemma_A_2 P hP η T' w' pA' pS').mp hsub'
    have hT' := (feasible_iff P hP η wN pAN pSN T' hN hq).mp ⟨hp', hs'⟩
    exact hopt T' hT'

lemma unc_iff (P : Params) (hP : P.Standing) (η T w pA pS : ℝ) :
    IsUnconstrainedFeeOptimal P η T w pA pS ↔
      (w = wF_star P η T ∧ pA = pAF_star P η T ∧ pS = pSF_star P η T) ∧
        ∀ x, phi P η x ≤ phi P η T := by
  constructor
  · rintro ⟨hsub, hopt⟩
    obtain ⟨rfl, rfl, rfl⟩ := (lemma_A_2 P hP η T w pA pS).mp hsub
    exact ⟨⟨rfl, rfl, rfl⟩, fun x => hopt x _ _ _ ((lemma_A_2 P hP η x _ _ _).mpr ⟨rfl, rfl, rfl⟩)⟩
  · rintro ⟨⟨rfl, rfl, rfl⟩, hopt⟩
    refine ⟨(lemma_A_2 P hP η T _ _ _).mpr ⟨rfl, rfl, rfl⟩, ?_⟩
    intro T' w' pA' pS' hsub'
    obtain ⟨rfl, rfl, rfl⟩ := (lemma_A_2 P hP η T' w' pA' pS').mp hsub'
    exact hopt T'


/-- Amazon's unconstrained optimal fee: the vertex of `phi P η`. -/
noncomputable def Tt (P : Params) (η : ℝ) : ℝ :=
  -(phi P η 1 - phi P η 0 - aF P η) / (2 * aF P η)

lemma aF_const (P : Params) (hP : P.Standing) (η : ℝ) : aF P η = aF P 0 := by
  rw [aF_val P hP η, aF_val P hP 0]

lemma Tt_opt (P : Params) (hP : P.Standing) (η T : ℝ) :
    (∀ x, phi P η x ≤ phi P η T) ↔ T = Tt P η :=
  vtx_global (phi P η) _ _ _ _ (aF_neg P hP η) (phi_quad P η)

lemma shiftW (P : Params) (η : ℝ) : wF_star P η 1 = wF_star P η 0 + (wF_star P 0 1 - wF_star P 0 0) := by
  simp only [wF_star]; ring
lemma shiftA (P : Params) (η : ℝ) : pAF_star P η 1 = pAF_star P η 0 + (pAF_star P 0 1 - pAF_star P 0 0) := by
  simp only [pAF_star]; ring
lemma shiftS (P : Params) (η : ℝ) : pSF_star P η 1 = pSF_star P η 0 + (pSF_star P 0 1 - pSF_star P 0 0) := by
  simp only [pSF_star]; ring
lemma aff0W (P : Params) (a b t : ℝ) :
    wF_star P ((1 - t) * a + t * b) 0 = (1 - t) * wF_star P a 0 + t * wF_star P b 0 := by
  simp only [wF_star]; ring
lemma aff0A (P : Params) (a b t : ℝ) :
    pAF_star P ((1 - t) * a + t * b) 0 = (1 - t) * pAF_star P a 0 + t * pAF_star P b 0 := by
  simp only [pAF_star]; ring
lemma aff0S (P : Params) (a b t : ℝ) :
    pSF_star P ((1 - t) * a + t * b) 0 = (1 - t) * pSF_star P a 0 + t * pSF_star P b 0 := by
  simp only [pSF_star]; ring

lemma Pi_diff_aff (P : Params) (a b t w1 A1 S1 w2 A2 S2 dw dA dS : ℝ) :
    profitAF P ((1 - t) * a + t * b) 1 ((1 - t) * w1 + t * w2 + dw) ((1 - t) * A1 + t * A2 + dA)
        ((1 - t) * S1 + t * S2 + dS) -
      profitAF P ((1 - t) * a + t * b) 0 ((1 - t) * w1 + t * w2) ((1 - t) * A1 + t * A2)
        ((1 - t) * S1 + t * S2) =
    (1 - t) * (profitAF P a 1 (w1 + dw) (A1 + dA) (S1 + dS) - profitAF P a 0 w1 A1 S1) +
      t * (profitAF P b 1 (w2 + dw) (A2 + dA) (S2 + dS) - profitAF P b 0 w2 A2 S2) := by
  simp only [profitAF, qAF, qSF]; ring

lemma bnum_aff (P : Params) (a b t : ℝ) :
    phi P ((1 - t) * a + t * b) 1 - phi P ((1 - t) * a + t * b) 0 =
      (1 - t) * (phi P a 1 - phi P a 0) + t * (phi P b 1 - phi P b 0) := by
  unfold phi
  rw [shiftW P ((1 - t) * a + t * b), shiftA P ((1 - t) * a + t * b), shiftS P ((1 - t) * a + t * b),
    aff0W, aff0A, aff0S, shiftW P a, shiftA P a, shiftS P a, shiftW P b, shiftA P b, shiftS P b]
  exact Pi_diff_aff P a b t _ _ _ _ _ _ _ _ _

lemma aff_Tt (P : Params) (hP : P.Standing) (a b t : ℝ) :
    Tt P ((1 - t) * a + t * b) = (1 - t) * Tt P a + t * Tt P b := by
  have h0 := (aF_neg P hP 0).ne
  unfold Tt
  rw [aF_const P hP ((1 - t) * a + t * b), aF_const P hP a, aF_const P hP b, bnum_aff]
  field_simp; ring


lemma aff_Tbs (P : Params) (a b t : ℝ) :
    Tbar P ((1 - t) * a + t * b) = (1 - t) * (Tbar P a) + t * (Tbar P b) := by
  simp only [wN_star, pAN_star, pSN_star, wF_star, pAF_star, pSF_star, Tbar]; ring


lemma phi_vertex (P : Params) (hP : P.Standing) (η x : ℝ) :
    phi P η x = phi P η (Tt P η) + aF P η * (x - Tt P η) ^ 2 := by
  have ha := (aF_neg P hP η).ne
  rw [phi_quad P η x, phi_quad P η (Tt P η)]
  unfold Tt
  field_simp
  ring

lemma gain_vertex (P : Params) (hP : P.Standing) (η : ℝ) :
    gain P η (wN_star P η) (pAN_star P η) (pSN_star P η) (Tt P η) (wF_star P η (Tt P η))
        (pAF_star P η (Tt P η)) (pSF_star P η (Tt P η)) =
      gain P η (wN_star P η) (pAN_star P η) (pSN_star P η) (Tbar P η) (wF_star P η (Tbar P η))
        (pAF_star P η (Tbar P η)) (pSF_star P η (Tbar P η)) - aF P η * (Tbar P η - Tt P η) ^ 2 := by
  have e2 := phi_vertex P hP η (Tbar P η)
  unfold gain
  change phi P η (Tt P η) - _ = phi P η (Tbar P η) - _ - _
  rw [e2]; ring

end FBAComp.AmazonGain

open FBAComp.AmazonGain in
theorem solution (P : Params) (hP : P.Standing) :
    ∀ η₁ η₂ : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ ηm : ℝ,
      ηm = (1 - t) * η₁ + t * η₂ →
      ∀ wN₁ pAN₁ pSN₁ T₁ wF₁ pAF₁ pSF₁ : ℝ,
      ∀ wN₂ pAN₂ pSN₂ T₂ wF₂ pAF₂ pSF₂ : ℝ,
      ∀ wNm pANm pSNm Tm wFm pAFm pSFm : ℝ,
        IsEqN P η₁ wN₁ pAN₁ pSN₁ →
        IsUnconstrainedFeeOptimal P η₁ T₁ wF₁ pAF₁ pSF₁ →
        IsEqN P η₂ wN₂ pAN₂ pSN₂ →
        IsUnconstrainedFeeOptimal P η₂ T₂ wF₂ pAF₂ pSF₂ →
        IsEqN P ηm wNm pANm pSNm →
        IsUnconstrainedFeeOptimal P ηm Tm wFm pAFm pSFm →
        gain P ηm wNm pANm pSNm Tm wFm pAFm pSFm ≤
          (1 - t) * gain P η₁ wN₁ pAN₁ pSN₁ T₁ wF₁ pAF₁ pSF₁ +
            t * gain P η₂ wN₂ pAN₂ pSN₂ T₂ wF₂ pAF₂ pSF₂ := by
  intro η₁ η₂ t ht ηm hm wN₁ pAN₁ pSN₁ T₁ wF₁ pAF₁ pSF₁ wN₂ pAN₂ pSN₂ T₂ wF₂ pAF₂ pSF₂
    wNm pANm pSNm Tm wFm pAFm pSFm h1 h1' h2 h2' h3 h3'
  obtain ⟨rfl, rfl, rfl⟩ := (lemma_A_1 P hP _ _ _ _).mp h1
  obtain ⟨rfl, rfl, rfl⟩ := (lemma_A_1 P hP _ _ _ _).mp h2
  obtain ⟨rfl, rfl, rfl⟩ := (lemma_A_1 P hP _ _ _ _).mp h3
  obtain ⟨⟨rfl, rfl, rfl⟩, o1⟩ := (unc_iff P hP _ _ _ _ _).mp h1'
  obtain ⟨⟨rfl, rfl, rfl⟩, o2⟩ := (unc_iff P hP _ _ _ _ _).mp h2'
  obtain ⟨⟨rfl, rfl, rfl⟩, o3⟩ := (unc_iff P hP _ _ _ _ _).mp h3'
  obtain rfl := (Tt_opt P hP _ _).mp o1
  obtain rfl := (Tt_opt P hP _ _).mp o2
  obtain rfl := (Tt_opt P hP _ _).mp o3
  rw [gain_vertex P hP η₁, gain_vertex P hP η₂, gain_vertex P hP ηm]
  have hc := prop2_convexity_Tbar P hP η₁ η₂ t ht ηm hm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    ((lemma_A_1 P hP _ _ _ _).mpr ⟨rfl, rfl, rfl⟩) ((lemma_A_2 P hP _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩)
    ((lemma_A_1 P hP _ _ _ _).mpr ⟨rfl, rfl, rfl⟩) ((lemma_A_2 P hP _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩)
    ((lemma_A_1 P hP _ _ _ _).mpr ⟨rfl, rfl, rfl⟩) ((lemma_A_2 P hP _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩)
  rw [aF_const P hP η₁, aF_const P hP η₂, aF_const P hP ηm]
  have ha := aF_neg P hP 0
  have hd : Tbar P ηm - Tt P ηm =
      (1 - t) * (Tbar P η₁ - Tt P η₁) + t * (Tbar P η₂ - Tt P η₂) := by
    rw [hm, aff_Tbs, aff_Tt P hP]; ring
  have hsq : (Tbar P ηm - Tt P ηm) ^ 2 ≤
      (1 - t) * (Tbar P η₁ - Tt P η₁) ^ 2 + t * (Tbar P η₂ - Tt P η₂) ^ 2 := by
    rw [hd]
    obtain ⟨t0, t1⟩ := ht
    nlinarith [mul_nonneg (mul_nonneg t0 (sub_nonneg.mpr t1))
      (sq_nonneg ((Tbar P η₁ - Tt P η₁) - (Tbar P η₂ - Tt P η₂)))]
  nlinarith [mul_le_mul_of_nonneg_left hsq (neg_nonneg.mpr ha.le)]
