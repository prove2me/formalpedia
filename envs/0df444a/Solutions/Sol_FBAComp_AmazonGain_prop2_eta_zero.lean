-- Prove2me | solution 1 for FBAComp.AmazonGain.prop2_eta_zero
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-10-20T03:42:12.917992+00:00
-- url     : https://prove2.me/submissions/87de2a31-da60-4d9b-a4be-6f0f683ac75f

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


/-- The counterexample parameters. -/
noncomputable def P0 : Params := ⟨1/10, 1/10, 1/10, 1/2, 2, 1, 1/10, 0, 10, 0⟩

lemma P0_standing : P0.Standing := by
  unfold Params.Standing P0; norm_num

lemma nashN0 (η w pA pS : ℝ) : IsPriceNE_N P0 η w pA pS ↔
    pA = (-124/149:ℝ)*η + (80/149:ℝ)*w + (142/745:ℝ) ∧ pS = (-180/149:ℝ)*η + (20/149:ℝ)*w + (22/149:ℝ) := by
  rw [nashN_iff P0 (by norm_num [P0])]
  simp only [P0]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

lemma eqN0 (η w pA pS : ℝ) : IsEqN P0 η w pA pS ↔
    w = (-23/28:ℝ)*η + (1039/200:ℝ) ∧ pA = (-1328/1043:ℝ)*η + (444/149:ℝ) ∧ pS = (-1375/1043:ℝ)*η + (1259/1490:ℝ) := by
  constructor
  · rintro ⟨hN, hopt⟩
    obtain ⟨hA, hS⟩ := (nashN0 η w pA pS).mp hN
    obtain ⟨W, hW⟩ : ∃ W : ℝ, W = (-23/28:ℝ)*η + (1039/200:ℝ) := ⟨_, rfl⟩
    have h := hopt W _ _ ((nashN0 η W _ _).mpr ⟨rfl, rfl⟩)
    simp only [profitMN, qAN, P0] at h
    rw [hA, hS, hW] at h
    have hsq : (w - W) ^ 2 ≤ 0 := by rw [hW]; nlinarith
    have hw : w = W := by nlinarith [sq_nonneg (w - W)]
    refine ⟨hw.trans hW, ?_, ?_⟩
    · rw [hA, hw, hW]; ring
    · rw [hS, hw, hW]; ring
  · rintro ⟨hw, hA, hS⟩
    refine ⟨(nashN0 η w pA pS).mpr ⟨by rw [hA, hw]; ring, by rw [hS, hw]; ring⟩, ?_⟩
    intro w' pA' pS' h'
    obtain ⟨hA', hS'⟩ := (nashN0 η w' pA' pS').mp h'
    simp only [profitMN, qAN, P0]
    rw [hA', hS', hA, hS, hw]
    nlinarith [sq_nonneg (w' - ((-23/28:ℝ)*η + (1039/200:ℝ)))]

lemma nashF0 (η T w pA pS : ℝ) : IsPriceNE_F P0 η T w pA pS ↔
    pA = (-204/149:ℝ)*η + (80/149:ℝ)*w + (580/1341:ℝ)*T + (153/745:ℝ) ∧ pS = (-200/149:ℝ)*η + (20/149:ℝ)*w + (890/1341:ℝ)*T + (30/149:ℝ) := by
  rw [nashF_iff P0 (by norm_num [P0])]
  simp only [P0]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

lemma eqF0 (η T w pA pS : ℝ) : IsSubgameEqF P0 η T w pA pS ↔
    w = (-97/70:ℝ)*η + (-3/28:ℝ)*T + (7291/1400:ℝ) ∧ pA = (-2204/1043:ℝ)*η + (3520/9387:ℝ)*T + (15653/5215:ℝ) ∧ pS = (-1594/1043:ℝ)*η + (6095/9387:ℝ)*T + (9391/10430:ℝ) := by
  constructor
  · rintro ⟨hN, hopt⟩
    obtain ⟨hA, hS⟩ := (nashF0 η T w pA pS).mp hN
    obtain ⟨W, hW⟩ : ∃ W : ℝ, W = (-97/70:ℝ)*η + (-3/28:ℝ)*T + (7291/1400:ℝ) := ⟨_, rfl⟩
    have h := hopt W _ _ ((nashF0 η T W _ _).mpr ⟨rfl, rfl⟩)
    simp only [profitMF, qAF, P0] at h
    rw [hA, hS, hW] at h
    have hsq : (w - W) ^ 2 ≤ 0 := by rw [hW]; nlinarith
    have hw : w = W := by nlinarith [sq_nonneg (w - W)]
    refine ⟨hw.trans hW, ?_, ?_⟩
    · rw [hA, hw, hW]; ring
    · rw [hS, hw, hW]; ring
  · rintro ⟨hw, hA, hS⟩
    refine ⟨(nashF0 η T w pA pS).mpr ⟨by rw [hA, hw]; ring, by rw [hS, hw]; ring⟩, ?_⟩
    intro w' pA' pS' h'
    obtain ⟨hA', hS'⟩ := (nashF0 η T w' pA' pS').mp h'
    simp only [profitMF, qAF, P0]
    rw [hA', hS', hA, hS, hw]
    nlinarith [sq_nonneg (w' - ((-97/70:ℝ)*η + (-3/28:ℝ)*T + (7291/1400:ℝ)))]

lemma P0_interior : Interior P0 := by
  intro η hη w pA pS h
  obtain ⟨hw, hA, hS⟩ := (eqN0 η w pA pS).mp h
  have h1 : η < 1/10 := by simpa [P0] using hη.2
  simp only [qSN, P0]
  rw [hA, hS]
  nlinarith [hη.1]


lemma feeOpt0 (η : ℝ) (h0 : 0 ≤ η) (h1 : η ≤ 1/100) :
    IsFeeOptimal P0 η (profitSN P0 η ((-1328/1043:ℝ)*η + (444/149:ℝ)) ((-1375/1043:ℝ)*η + (1259/1490:ℝ)))
      ((-16576542/9327845:ℝ)*η + (-67105431/1212619850:ℝ)) ((-97/70:ℝ)*η + (-3/28:ℝ)*((-16576542/9327845:ℝ)*η + (-67105431/1212619850:ℝ)) + (7291/1400:ℝ)) ((-2204/1043:ℝ)*η + (3520/9387:ℝ)*((-16576542/9327845:ℝ)*η + (-67105431/1212619850:ℝ)) + (15653/5215:ℝ)) ((-1594/1043:ℝ)*η + (6095/9387:ℝ)*((-16576542/9327845:ℝ)*η + (-67105431/1212619850:ℝ)) + (9391/10430:ℝ)) := by
  have hI : 0 ≤ η * (1/100 - η) := mul_nonneg h0 (by linarith)
  refine ⟨(eqF0 η _ _ _ _).mpr ⟨rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · simp only [profitSN, profitSF, qSN, qSF, P0]
    nlinarith
  · simp only [qSF, P0]
    nlinarith
  · intro T' w' pA' pS' h' _ _
    obtain ⟨hw, hA, hS⟩ := (eqF0 η T' w' pA' pS').mp h'
    simp only [profitAF, qAF, qSF, P0]
    rw [hw, hA, hS]
    nlinarith [sq_nonneg (T' - ((-16576542/9327845:ℝ)*η + (-67105431/1212619850:ℝ)))]

lemma gain0 (η : ℝ) (h0 : 0 ≤ η) (h1 : η ≤ 1/100) :
    profitAF P0 η ((-16576542/9327845:ℝ)*η + (-67105431/1212619850:ℝ)) ((-97/70:ℝ)*η + (-3/28:ℝ)*((-16576542/9327845:ℝ)*η + (-67105431/1212619850:ℝ)) + (7291/1400:ℝ)) ((-2204/1043:ℝ)*η + (3520/9387:ℝ)*((-16576542/9327845:ℝ)*η + (-67105431/1212619850:ℝ)) + (15653/5215:ℝ)) ((-1594/1043:ℝ)*η + (6095/9387:ℝ)*((-16576542/9327845:ℝ)*η + (-67105431/1212619850:ℝ)) + (9391/10430:ℝ)) <
      profitAN P0 η ((-23/28:ℝ)*η + (1039/200:ℝ)) ((-1328/1043:ℝ)*η + (444/149:ℝ)) ((-1375/1043:ℝ)*η + (1259/1490:ℝ)) := by
  have hI : 0 ≤ η * (1/100 - η) := mul_nonneg h0 (by linarith)
  simp only [profitAF, profitAN, qAF, qSF, qAN, qSN, P0]
  nlinarith

end FBAComp.AmazonGain

open FBAComp.AmazonGain in
theorem solution : ¬ (∀ (P : Params) (hP : P.Standing) (hI : Interior P)
    (wN pAN pSN T wF pAF pSF : ℝ)
    (hN : IsEqN P 0 wN pAN pSN)
    (hF : IsFeeOptimal P 0 (profitSN P 0 pAN pSN) T wF pAF pSF),
    0 < gain P 0 wN pAN pSN T wF pAF pSF) := by
  intro h
  have h1 := h P0 P0_standing P0_interior _ _ _ _ _ _ _
    ((eqN0 0 _ _ _).mpr ⟨rfl, rfl, rfl⟩) (feeOpt0 0 le_rfl (by norm_num))
  have h2 := gain0 0 le_rfl (by norm_num)
  unfold gain at h1
  linarith
