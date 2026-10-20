-- Prove2me | solution 1 for FBAComp.AmazonGain.lemma_A_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T03:49:22.056843+00:00
-- url     : https://prove2.me/submissions/86dcc70a-dcb1-4af9-9ba2-b7cc03c7152f

import Mathlib
import Definitions.Def_FBAComp_AmazonGain_ClosedForms

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


lemma lin_diff (r β a s d : ℝ) (hr : r < 1) (hD : 0 < 4 - (1 + r) * β ^ 2)
    (h1 : 2 * a = (1 + r) * β * s + d) (h2 : 2 * (1 - r) * s = (1 - r) * β * a) :
    a = 2 * d / (4 - (1 + r) * β ^ 2) ∧ s = β * d / (4 - (1 + r) * β ^ 2) := by
  have hs : 2 * s = β * a := by
    have h3 : (1 - r) * (2 * s - β * a) = 0 := by linear_combination h2
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h (by linarith)
    · linarith
  have ha : a * (4 - (1 + r) * β ^ 2) = 2 * d := by linear_combination 2 * h1 + (1 + r) * β * hs
  refine ⟨by rw [eq_div_iff hD.ne']; linarith, ?_⟩
  rw [eq_div_iff hD.ne']
  linear_combination (1/2 : ℝ) * β * ha + (4 - (1 + r) * β ^ 2) / 2 * hs

lemma oem_le (k c0 W q x : ℝ) (hk : 0 < k) (hq : q = k * (W - c0)) :
    (x - c0) * (q - k * (x - W)) ≤ (W - c0) * q := by
  subst hq; nlinarith [mul_nonneg hk.le (sq_nonneg (x - W))]

lemma oem_eq (k c0 W q x : ℝ) (hk : 0 < k) (hq : q = k * (W - c0))
    (h : (W - c0) * q ≤ (x - c0) * (q - k * (x - W))) : x = W := by
  subst hq
  have h2 : k * (x - W) ^ 2 ≤ 0 := by nlinarith
  have h3 : (x - W) ^ 2 ≤ 0 := by
    by_contra hc; push Not at hc; nlinarith [mul_pos hk hc]
  nlinarith [sq_nonneg (x - W)]


lemma starN_E1 (P : Params) (hP : P.Standing) (η : ℝ) :
    2 * (pAN_star P η) = P.QA + P.β * (pSN_star P η) + P.α * P.sA - η * P.sS + wN_star P η + P.c + P.r * P.β * (pSN_star P η) := by
  obtain ⟨_, _, hb0, hb1, hr0, hr1, _⟩ := hP
  have h1 : (1 - P.r) ≠ 0 := by nlinarith
  have h2 : (4 - (1 + P.r) * P.β ^ 2) ≠ 0 := by nlinarith
  have h3 : (2 - P.β ^ 2) ≠ 0 := by nlinarith
  simp only [wN_star, pAN_star, pSN_star, wF_star, pAF_star, pSF_star]
  generalize hD : (4 - (1 + P.r) * P.β ^ 2) = D at h2 ⊢
  generalize hE : (2 - P.β ^ 2) = E at h3 ⊢
  generalize hR : (1 - P.r) = R at h1 ⊢
  field_simp
  subst hD hE hR
  ring

lemma starN_E2 (P : Params) (hP : P.Standing) (η : ℝ) :
    2 * (1 - P.r) * (pSN_star P η) = (1 - P.r) * (P.QS + P.β * (pAN_star P η) + P.α * P.sS - η * P.sA) + P.g + P.c := by
  obtain ⟨_, _, hb0, hb1, hr0, hr1, _⟩ := hP
  have h1 : (1 - P.r) ≠ 0 := by nlinarith
  have h2 : (4 - (1 + P.r) * P.β ^ 2) ≠ 0 := by nlinarith
  have h3 : (2 - P.β ^ 2) ≠ 0 := by nlinarith
  simp only [wN_star, pAN_star, pSN_star, wF_star, pAF_star, pSF_star]
  generalize hD : (4 - (1 + P.r) * P.β ^ 2) = D at h2 ⊢
  generalize hE : (2 - P.β ^ 2) = E at h3 ⊢
  generalize hR : (1 - P.r) = R at h1 ⊢
  field_simp
  subst hD hE hR
  ring

lemma starN_foc (P : Params) (hP : P.Standing) (η : ℝ) :
    qAN P η (pAN_star P η) (pSN_star P η) =
      (2 - P.β ^ 2) / (4 - (1 + P.r) * P.β ^ 2) * (wN_star P η - P.c0) := by
  obtain ⟨_, _, hb0, hb1, hr0, hr1, _⟩ := hP
  have h1 : (1 - P.r) ≠ 0 := by nlinarith
  have h2 : (4 - (1 + P.r) * P.β ^ 2) ≠ 0 := by nlinarith
  have h3 : (2 - P.β ^ 2) ≠ 0 := by nlinarith
  simp only [qAN, wN_star, pAN_star, pSN_star, wF_star, pAF_star, pSF_star]
  generalize hD : (4 - (1 + P.r) * P.β ^ 2) = D at h2 ⊢
  generalize hE : (2 - P.β ^ 2) = E at h3 ⊢
  generalize hR : (1 - P.r) = R at h1 ⊢
  field_simp
  subst hD hE hR
  ring

lemma eqN_iff (P : Params) (hP : P.Standing) (η w pA pS : ℝ) :
    IsEqN P η w pA pS ↔
      w = wN_star P η ∧ pA = pAN_star P η ∧ pS = pSN_star P η := by
  have hr : P.r < 1 := hP.2.2.2.2.2.1
  have hb0 : 0 < P.β := hP.2.2.1
  have hb1 : P.β < 1 := hP.2.2.2.1
  have hr0 : 0 < P.r := hP.2.2.2.2.1
  have hD : 0 < 4 - (1 + P.r) * P.β ^ 2 := by nlinarith
  have hk : 0 < (2 - P.β ^ 2) / (4 - (1 + P.r) * P.β ^ 2) := div_pos (by nlinarith) hD
  have hstar : IsPriceNE_N P η (wN_star P η) (pAN_star P η) (pSN_star P η) :=
    (nashN_iff P hr η _ _ _).mpr ⟨starN_E1 P hP η, starN_E2 P hP η⟩
  have hq : ∀ w' pA' pS', IsPriceNE_N P η w' pA' pS' →
      qAN P η pA' pS' = qAN P η (pAN_star P η) (pSN_star P η) -
        (2 - P.β ^ 2) / (4 - (1 + P.r) * P.β ^ 2) * (w' - wN_star P η) := by
    intro w' pA' pS' h'
    obtain ⟨e1, e2⟩ := (nashN_iff P hr η _ _ _).mp h'
    have s1 := starN_E1 P hP η
    have s2 := starN_E2 P hP η
    obtain ⟨da, ds⟩ := lin_diff P.r P.β (pA' - pAN_star P η) (pS' - pSN_star P η) (w' - wN_star P η) hr hD
      (by linear_combination e1 - s1) (by linear_combination e2 - s2)
    have : qAN P η pA' pS' - qAN P η (pAN_star P η) (pSN_star P η) = -(pA' - pAN_star P η) + P.β * (pS' - pSN_star P η) := by
      unfold qAN; ring
    rw [show qAN P η pA' pS' = qAN P η (pAN_star P η) (pSN_star P η) + (-(pA' - pAN_star P η) + P.β * (pS' - pSN_star P η)) by linarith,
      da, ds]
    field_simp
    ring
  constructor
  · rintro ⟨hN, hopt⟩
    have h := hopt _ _ _ hstar
    unfold profitMN at h
    rw [hq w pA pS hN] at h
    have hw := oem_eq _ P.c0 _ _ w hk (starN_foc P hP η) h
    obtain ⟨e1, e2⟩ := (nashN_iff P hr η _ _ _).mp hN
    have s1 := starN_E1 P hP η
    have s2 := starN_E2 P hP η
    obtain ⟨da, ds⟩ := lin_diff P.r P.β (pA - pAN_star P η) (pS - pSN_star P η) (w - wN_star P η) hr hD
      (by linear_combination e1 - s1) (by linear_combination e2 - s2)
    rw [hw, sub_self, mul_zero, zero_div] at da ds
    exact ⟨hw, by linarith, by linarith⟩
  · rintro ⟨rfl, rfl, rfl⟩
    refine ⟨hstar, fun w' pA' pS' h' => ?_⟩
    unfold profitMN
    rw [hq w' pA' pS' h']
    exact oem_le _ P.c0 _ _ w' hk (starN_foc P hP η)

lemma starF_E1 (P : Params) (hP : P.Standing) (η : ℝ) (T : ℝ) :
    2 * (pAF_star P η T) = P.QA + P.β * (pSF_star P η T) + P.α * P.sA - η * P.sA + wF_star P η T + P.c + P.β * (P.r * (pSF_star P η T) + T - P.c) := by
  obtain ⟨_, _, hb0, hb1, hr0, hr1, _⟩ := hP
  have h1 : (1 - P.r) ≠ 0 := by nlinarith
  have h2 : (4 - (1 + P.r) * P.β ^ 2) ≠ 0 := by nlinarith
  have h3 : (2 - P.β ^ 2) ≠ 0 := by nlinarith
  simp only [wN_star, pAN_star, pSN_star, wF_star, pAF_star, pSF_star]
  generalize hD : (4 - (1 + P.r) * P.β ^ 2) = D at h2 ⊢
  generalize hE : (2 - P.β ^ 2) = E at h3 ⊢
  generalize hR : (1 - P.r) = R at h1 ⊢
  field_simp
  subst hD hE hR
  ring

lemma starF_E2 (P : Params) (hP : P.Standing) (η : ℝ) (T : ℝ) :
    2 * (1 - P.r) * (pSF_star P η T) = (1 - P.r) * (P.QS + P.β * (pAF_star P η T) + P.α * P.sA - η * P.sA) + P.g + T := by
  obtain ⟨_, _, hb0, hb1, hr0, hr1, _⟩ := hP
  have h1 : (1 - P.r) ≠ 0 := by nlinarith
  have h2 : (4 - (1 + P.r) * P.β ^ 2) ≠ 0 := by nlinarith
  have h3 : (2 - P.β ^ 2) ≠ 0 := by nlinarith
  simp only [wN_star, pAN_star, pSN_star, wF_star, pAF_star, pSF_star]
  generalize hD : (4 - (1 + P.r) * P.β ^ 2) = D at h2 ⊢
  generalize hE : (2 - P.β ^ 2) = E at h3 ⊢
  generalize hR : (1 - P.r) = R at h1 ⊢
  field_simp
  subst hD hE hR
  ring

lemma starF_foc (P : Params) (hP : P.Standing) (η : ℝ) (T : ℝ) :
    qAF P η (pAF_star P η T) (pSF_star P η T) =
      (2 - P.β ^ 2) / (4 - (1 + P.r) * P.β ^ 2) * (wF_star P η T - P.c0) := by
  obtain ⟨_, _, hb0, hb1, hr0, hr1, _⟩ := hP
  have h1 : (1 - P.r) ≠ 0 := by nlinarith
  have h2 : (4 - (1 + P.r) * P.β ^ 2) ≠ 0 := by nlinarith
  have h3 : (2 - P.β ^ 2) ≠ 0 := by nlinarith
  simp only [qAF, wN_star, pAN_star, pSN_star, wF_star, pAF_star, pSF_star]
  generalize hD : (4 - (1 + P.r) * P.β ^ 2) = D at h2 ⊢
  generalize hE : (2 - P.β ^ 2) = E at h3 ⊢
  generalize hR : (1 - P.r) = R at h1 ⊢
  field_simp
  subst hD hE hR
  ring

lemma eqF_iff (P : Params) (hP : P.Standing) (η T w pA pS : ℝ) :
    IsSubgameEqF P η T w pA pS ↔
      w = wF_star P η T ∧ pA = pAF_star P η T ∧ pS = pSF_star P η T := by
  have hr : P.r < 1 := hP.2.2.2.2.2.1
  have hb0 : 0 < P.β := hP.2.2.1
  have hb1 : P.β < 1 := hP.2.2.2.1
  have hr0 : 0 < P.r := hP.2.2.2.2.1
  have hD : 0 < 4 - (1 + P.r) * P.β ^ 2 := by nlinarith
  have hk : 0 < (2 - P.β ^ 2) / (4 - (1 + P.r) * P.β ^ 2) := div_pos (by nlinarith) hD
  have hstar : IsPriceNE_F P η T (wF_star P η T) (pAF_star P η T) (pSF_star P η T) :=
    (nashF_iff P hr η T _ _ _).mpr ⟨starF_E1 P hP η T, starF_E2 P hP η T⟩
  have hq : ∀ w' pA' pS', IsPriceNE_F P η T w' pA' pS' →
      qAF P η pA' pS' = qAF P η (pAF_star P η T) (pSF_star P η T) -
        (2 - P.β ^ 2) / (4 - (1 + P.r) * P.β ^ 2) * (w' - wF_star P η T) := by
    intro w' pA' pS' h'
    obtain ⟨e1, e2⟩ := (nashF_iff P hr η T _ _ _).mp h'
    have s1 := starF_E1 P hP η T
    have s2 := starF_E2 P hP η T
    obtain ⟨da, ds⟩ := lin_diff P.r P.β (pA' - pAF_star P η T) (pS' - pSF_star P η T) (w' - wF_star P η T) hr hD
      (by linear_combination e1 - s1) (by linear_combination e2 - s2)
    have : qAF P η pA' pS' - qAF P η (pAF_star P η T) (pSF_star P η T) = -(pA' - pAF_star P η T) + P.β * (pS' - pSF_star P η T) := by
      unfold qAF; ring
    rw [show qAF P η pA' pS' = qAF P η (pAF_star P η T) (pSF_star P η T) + (-(pA' - pAF_star P η T) + P.β * (pS' - pSF_star P η T)) by linarith,
      da, ds]
    field_simp
    ring
  constructor
  · rintro ⟨hN, hopt⟩
    have h := hopt _ _ _ hstar
    unfold profitMF at h
    rw [hq w pA pS hN] at h
    have hw := oem_eq _ P.c0 _ _ w hk (starF_foc P hP η T) h
    obtain ⟨e1, e2⟩ := (nashF_iff P hr η T _ _ _).mp hN
    have s1 := starF_E1 P hP η T
    have s2 := starF_E2 P hP η T
    obtain ⟨da, ds⟩ := lin_diff P.r P.β (pA - pAF_star P η T) (pS - pSF_star P η T) (w - wF_star P η T) hr hD
      (by linear_combination e1 - s1) (by linear_combination e2 - s2)
    rw [hw, sub_self, mul_zero, zero_div] at da ds
    exact ⟨hw, by linarith, by linarith⟩
  · rintro ⟨rfl, rfl, rfl⟩
    refine ⟨hstar, fun w' pA' pS' h' => ?_⟩
    unfold profitMF
    rw [hq w' pA' pS' h']
    exact oem_le _ P.c0 _ _ w' hk (starF_foc P hP η T)

end FBAComp.AmazonGain

open FBAComp.AmazonGain in
theorem solution (P : Params) (hP : P.Standing) (η T w pA pS : ℝ) :
    IsSubgameEqF P η T w pA pS ↔
      w = wF_star P η T ∧ pA = pAF_star P η T ∧ pS = pSF_star P η T :=
  eqF_iff P hP η T w pA pS
