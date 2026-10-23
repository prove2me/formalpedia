-- Prove2me | solution 1 for CrowdfundVC.Effects.proposition6
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-10-22T17:05:07.583749+00:00
-- url     : https://prove2.me/submissions/095019c6-ffb4-4880-835a-15f209bf7e83

import Definitions.Def_CrowdfundVC_Effects_Model

namespace CrowdfundVC.Effects

lemma cf6_kappa_ge {β v1 v2 R : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (h : R ≤ v1) :
    R ≤ kappa β v1 v2 R := by
  unfold kappa
  rw [if_neg (not_lt.mpr h)]
  have h2 : R ≤ max v2 R := le_max_right _ _
  nlinarith [mul_le_mul_of_nonneg_left h hβ0, mul_le_mul_of_nonneg_left h2 (sub_nonneg.2 hβ1)]

lemma cf6_kappa_eq {β v1 v2 R : ℝ} (h : R ≤ v1) (h2 : v2 ≤ R) :
    kappa β v1 v2 R = β * v1 + (1 - β) * R := by
  unfold kappa; rw [if_neg (not_lt.mpr h), max_eq_right h2]

lemma cf6_kappa_eq' {β v1 v2 R : ℝ} (h : R ≤ v1) :
    kappa β v1 v2 R = β * v1 + (1 - β) * max v2 R := by
  unfold kappa; rw [if_neg (not_lt.mpr h)]

lemma cf6_kappa_zero {β v1 v2 R : ℝ} (h : v1 < R) : kappa β v1 v2 R = 0 := by
  unfold kappa; rw [if_pos h]

lemma cf6_kappa_nonneg {β v1 v2 R : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hR : 0 ≤ R) :
    0 ≤ kappa β v1 v2 R := by
  by_cases h : v1 < R
  · rw [cf6_kappa_zero h]
  · push Not at h
    linarith [cf6_kappa_ge (v2 := v2) hβ0 hβ1 h]

lemma cf6_postS (P : Params) (p : ℝ) (hρ0 : 0 ≤ P.ρ) (hρ1 : P.ρ ≤ 1) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) :
    0 ≤ postS P p ∧ postS P p ≤ 1 ∧ p ≤ postS P p ∧
      (2 * P.ρ * p + 1 - P.ρ) * postS P p = (1 + P.ρ) * p := by
  unfold postS
  rcases eq_or_lt_of_le hp0 with h | h
  · subst h; simp
  · have hD : 0 < 2 * P.ρ * p + 1 - P.ρ := by
      nlinarith [mul_nonneg (sub_nonneg.2 hρ1) (sub_nonneg.2 hp1), mul_nonneg hρ0 hp0]
    refine ⟨div_nonneg (mul_nonneg (by linarith) hp0) hD.le, ?_, ?_, ?_⟩
    · rw [div_le_one hD]; nlinarith [mul_nonneg (sub_nonneg.2 hρ1) (sub_nonneg.2 hp1)]
    · rw [le_div_iff₀ hD]; nlinarith [mul_nonneg (mul_nonneg hρ0 hp0) (sub_nonneg.2 hp1)]
    · rw [mul_comm]; exact div_mul_cancel₀ _ hD.ne'

lemma cf6_postF (P : Params) (p : ℝ) (hρ0 : 0 ≤ P.ρ) (hρ1 : P.ρ ≤ 1) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) :
    0 ≤ postF P p ∧ postF P p ≤ p ∧
      (-2 * P.ρ * p + 1 + P.ρ) * postF P p = (1 - P.ρ) * p := by
  unfold postF
  have hD : 0 ≤ -2 * P.ρ * p + 1 + P.ρ := by nlinarith [mul_nonneg hρ0 (sub_nonneg.2 hp1)]
  rcases eq_or_lt_of_le hD with h | h
  · have hρ : P.ρ = 1 := by nlinarith [mul_nonneg hρ0 (sub_nonneg.2 hp1)]
    rw [← h, div_zero, hρ]
    exact ⟨le_refl _, hp0, by ring⟩
  · refine ⟨div_nonneg (mul_nonneg (by linarith) hp0) h.le, ?_, ?_⟩
    swap
    · rw [mul_comm]; exact div_mul_cancel₀ _ h.ne'
    rw [div_le_iff₀ h]; nlinarith [mul_nonneg (mul_nonneg hρ0 hp0) (sub_nonneg.2 hp1)]

lemma cf6_delta (P : Params) (A : ℝ) (hβ0 : 0 ≤ P.β) (hβ1 : P.β < 1)
    (hq0 : 0 ≤ probS P P.p1) (hq1 : probS P P.p1 ≤ 1)
    (hc0 : 0 ≤ (P.R0 - P.K) / P.R0) (hc1 : (P.R0 - P.K) / P.R0 ≤ 1)
    (hcR : (P.R0 - P.K) / P.R0 * P.R0 = P.R0 - P.K)
    (hA1 : P.R0 ≤ A * e1 P) (hA2 : A * e2 P ≤ P.R0) (hE : A * e1 P ≤ A * e1S P)
    (hsum : probS P P.p1 * e1S P + (1 - probS P P.p1) * e1F P = e1 P)
    (hA4 : probS P P.p1 * ((P.R0 - P.K) / P.R0 * A * e1S P
        - max ((P.R0 - P.K) / P.R0 * A * e2S P) (P.R0 - P.K)) ≤ A * e1 P - P.R0) :
    delta1 P A ≤ 0 := by
  have hS : alphaS P A = (P.R0 - P.K) / P.R0 * A := by unfold alphaS; ring
  unfold delta1 pi1Tilde pi1 pi1S pi1F
  rw [hS, cf6_kappa_eq hA1 hA2]
  have hSge : P.R0 - P.K ≤ (P.R0 - P.K) / P.R0 * A * e1S P := by
    have h1 : (P.R0 - P.K) / P.R0 * P.R0 ≤ (P.R0 - P.K) / P.R0 * (A * e1S P) :=
      mul_le_mul_of_nonneg_left (by linarith) hc0
    have h2 : (P.R0 - P.K) / P.R0 * A * e1S P = (P.R0 - P.K) / P.R0 * (A * e1S P) := by ring
    linarith
  rw [if_neg (not_lt.mpr hSge), cf6_kappa_eq' hSge]
  have hm : P.R0 - P.K ≤ max ((P.R0 - P.K) / P.R0 * A * e2S P) (P.R0 - P.K) := le_max_right _ _
  have hβ' : 0 ≤ 1 - P.β := by linarith
  by_cases hF : A * e1F P < P.R0
  · rw [if_pos hF]
    calc _ = (1 - P.β) * (probS P P.p1 * ((P.R0 - P.K) / P.R0 * A * e1S P
        - max ((P.R0 - P.K) / P.R0 * A * e2S P) (P.R0 - P.K)) - (A * e1 P - P.R0)) := by ring
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hβ' (by linarith)
  · push Not at hF
    rw [if_neg (not_lt.mpr hF), cf6_kappa_eq' hF]
    have hmF : P.R0 ≤ max (A * e2F P) P.R0 := le_max_right _ _
    have h1 : probS P P.p1 * ((P.R0 - P.K) / P.R0 * A * e1S P
        - max ((P.R0 - P.K) / P.R0 * A * e2S P) (P.R0 - P.K))
        ≤ probS P P.p1 * (A * e1S P - P.R0) := by
      apply mul_le_mul_of_nonneg_left _ hq0
      have : 0 ≤ (1 - (P.R0 - P.K) / P.R0) * (A * e1S P - P.R0) :=
        mul_nonneg (by linarith) (by linarith)
      linarith
    have h2 : (1 - probS P P.p1) * (A * e1F P - max (A * e2F P) P.R0)
        ≤ (1 - probS P P.p1) * (A * e1F P - P.R0) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have h3 : probS P P.p1 * (A * e1S P - P.R0) + (1 - probS P P.p1) * (A * e1F P - P.R0)
        - (A * e1 P - P.R0) = 0 := by linear_combination A * hsum
    calc _ = (1 - P.β) * (probS P P.p1 * ((P.R0 - P.K) / P.R0 * A * e1S P
        - max ((P.R0 - P.K) / P.R0 * A * e2S P) (P.R0 - P.K))
        + (1 - probS P P.p1) * (A * e1F P - max (A * e2F P) P.R0) - (A * e1 P - P.R0)) := by
          ring
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hβ' (by linarith)

theorem proposition6 (P : Params)
    (hRf0 : 0 ≤ P.Rf) (hRfR0 : P.Rf < P.R0) (hR0Rs : P.R0 < P.Rs) (hK0 : 0 < P.K)
    (hKR0 : P.K < P.R0) (hρ0 : 0 ≤ P.ρ) (hρ1 : P.ρ ≤ 1) (hβ0 : 0 ≤ P.β) (hβ1 : P.β < 1)
    (hp2 : 0 ≤ P.p2) (hp12 : P.p2 ≤ P.p1) (hp1 : P.p1 ≤ 1) (hpa0 : 0 ≤ P.pa) (hpa1 : P.pa ≤ 1)
    (hea : 0 < ea P) (hI : P.R0 ≤ e1S P) :
    (0 < P.ρ → P.p1 < 1 →
      P.R0 ≤ e1 P → 0 < deltaA P → invLevelCF P (alphaC P) < invLevelNoCF P (P.R0 / e1 P)) ∧
    (P.R0 ≤ e1 P → deltaA P ≤ 0 → invLevelNoCF P (P.R0 / e1 P) ≤ invLevelCF P (alphaC P)) ∧
    (e1 P < P.R0 →
      (∀ α : ℝ, 0 ≤ α → α ≤ 1 → invLevelNoCF P α = 0) ∧ 0 < invLevelCF P (alphaC P)) := by
  have hp1_0 : 0 ≤ P.p1 := le_trans hp2 hp12
  have hp2_1 : P.p2 ≤ 1 := le_trans hp12 hp1
  have hR0 : 0 < P.R0 := by linarith
  have hd : 0 < P.Rs - P.Rf := by linarith
  obtain ⟨hs1a, hs1b, hs1c, hs1d⟩ := cf6_postS P P.p1 hρ0 hρ1 hp1_0 hp1
  obtain ⟨hs2a, hs2b, hs2c, hs2d⟩ := cf6_postS P P.p2 hρ0 hρ1 hp2 hp2_1
  obtain ⟨hf1a, hf1b, hf1d⟩ := cf6_postF P P.p1 hρ0 hρ1 hp1_0 hp1
  have he1 : e1 P = P.Rf + P.p1 * (P.Rs - P.Rf) := by unfold e1 rev; ring
  have he2 : e2 P = P.Rf + P.p2 * (P.Rs - P.Rf) := by unfold e2 rev; ring
  have he1S : e1S P = P.Rf + postS P P.p1 * (P.Rs - P.Rf) := by unfold e1S rev; ring
  have he2S : e2S P = P.Rf + postS P P.p2 * (P.Rs - P.Rf) := by unfold e2S rev; ring
  have he1F : e1F P = P.Rf + postF P P.p1 * (P.Rs - P.Rf) := by unfold e1F rev; ring
  have hq : probS P P.p1 = (2 * P.ρ * P.p1 + 1 - P.ρ) / 2 := by unfold probS; ring
  have hh : probS P (1 / 2) = 1 / 2 := by unfold probS; ring
  have hp1pos : 0 < P.p1 := by
    rcases eq_or_lt_of_le hp1_0 with h | h
    · exfalso
      have h0 : postS P P.p1 = 0 := by unfold postS; rw [← h]; simp
      rw [he1S, h0] at hI; linarith
    · exact h
  have hD1 : 0 < 2 * P.ρ * P.p1 + 1 - P.ρ := by
    linarith [mul_nonneg (sub_nonneg.2 hρ1) (sub_nonneg.2 hp1), mul_nonneg hρ0 hp1_0]
  have hE1nn : 0 ≤ e1 P := by rw [he1]; linarith [mul_nonneg hp1_0 hd.le]
  have hE2S0 : 0 ≤ e2S P := by rw [he2S]; linarith [mul_nonneg hs2a hd.le]
  have hE1F0 : 0 ≤ e1F P := by rw [he1F]; linarith [mul_nonneg hf1a hd.le]
  have hE1S_pos : 0 < e1S P := by linarith
  have hE1le : e1 P ≤ e1S P := by
    rw [he1, he1S]; linarith [mul_le_mul_of_nonneg_right hs1c hd.le]
  have hE2le : e2 P ≤ e2S P := by
    rw [he2, he2S]; linarith [mul_le_mul_of_nonneg_right hs2c hd.le]
  have hE21 : e2 P ≤ e1 P := by
    rw [he1, he2]; linarith [mul_le_mul_of_nonneg_right hp12 hd.le]
  have hE1Fle : e1F P ≤ e1 P := by
    rw [he1F, he1]; linarith [mul_le_mul_of_nonneg_right hf1b hd.le]
  have hq0 : 0 < probS P P.p1 := by rw [hq]; linarith
  have hq1 : probS P P.p1 ≤ 1 := by rw [hq]; linarith [mul_nonneg hρ0 (sub_nonneg.2 hp1)]
  have hsum : probS P P.p1 * e1S P + (1 - probS P P.p1) * e1F P = e1 P := by
    rw [hq, he1S, he1F, he1]
    linear_combination ((P.Rs - P.Rf) / 2) * hs1d + ((P.Rs - P.Rf) / 2) * hf1d
  have hs12 : postS P P.p2 ≤ postS P P.p1 ∧
      probS P P.p1 * (postS P P.p1 - postS P P.p2) ≤ P.p1 - P.p2 := by
    rcases eq_or_lt_of_le hp2 with h | h
    · have h0 : postS P P.p2 = 0 := by unfold postS; rw [← h]; simp
      rw [h0, ← h, hq]
      refine ⟨hs1a, ?_⟩
      linarith [hs1d, mul_nonneg (sub_nonneg.2 hρ1) hp1_0]
    · have hD2 : 0 < 2 * P.ρ * P.p2 + 1 - P.ρ := by
        linarith [mul_nonneg (sub_nonneg.2 hρ1) (sub_nonneg.2 hp2_1), mul_nonneg hρ0 hp2]
      have key : (2 * P.ρ * P.p1 + 1 - P.ρ) * (2 * P.ρ * P.p2 + 1 - P.ρ)
          * (postS P P.p1 - postS P P.p2) = (1 + P.ρ) * (1 - P.ρ) * (P.p1 - P.p2) := by
        linear_combination (2 * P.ρ * P.p2 + 1 - P.ρ) * hs1d
          - (2 * P.ρ * P.p1 + 1 - P.ρ) * hs2d
      have hrhs : 0 ≤ (1 + P.ρ) * (1 - P.ρ) * (P.p1 - P.p2) :=
        mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
      have hmono : 0 ≤ postS P P.p1 - postS P P.p2 := by
        by_contra hcon; push Not at hcon
        have := mul_neg_of_pos_of_neg (mul_pos hD1 hD2) hcon
        linarith
      refine ⟨by linarith, ?_⟩
      rw [hq]
      by_contra hcon; push Not at hcon
      have h3 := mul_pos hD2 (by linarith : 0 < (2 * P.ρ * P.p1 + 1 - P.ρ) / 2
        * (postS P P.p1 - postS P P.p2) - (P.p1 - P.p2))
      linarith [mul_nonneg (add_nonneg (sq_nonneg (1 - P.ρ))
        (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hρ0) hp2)) (sub_nonneg.2 hp12)]
  have hc0 : 0 < (P.R0 - P.K) / P.R0 := div_pos (by linarith) hR0
  have hc1 : (P.R0 - P.K) / P.R0 < 1 := by rw [div_lt_one hR0]; linarith
  have hcR : (P.R0 - P.K) / P.R0 * P.R0 = P.R0 - P.K := div_mul_cancel₀ _ hR0.ne'
  have hE1S_E2S : e2S P ≤ e1S P := by
    rw [he1S, he2S]; linarith [mul_le_mul_of_nonneg_right hs12.1 hd.le]
  have hqE : probS P P.p1 * (e1S P - e2S P) ≤ e1 P - e2 P := by
    rw [he1S, he2S, he1, he2]
    have := mul_le_mul_of_nonneg_right hs12.2 hd.le
    linarith [this]
  -- the share α0 induces investment at t0
  have hInv : P.R0 ≤ alpha0 P * e1 P ∧ delta1 P (alpha0 P) ≤ 0 := by
    have hqc : probS P P.p1 * ((P.R0 - P.K) / P.R0) < 1 := by
      have := mul_le_of_le_one_left hc0.le hq1
      linarith
    have hden2 : 0 < e1 P - probS P P.p1 * e1S P * ((P.R0 - P.K) / P.R0) := by
      have h1 : 0 ≤ e1 P - probS P P.p1 * e1S P := by
        linarith [hsum, mul_nonneg (sub_nonneg.2 hq1) hE1F0]
      have h2 : 0 < probS P P.p1 * e1S P * (1 - (P.R0 - P.K) / P.R0) :=
        mul_pos (mul_pos hq0 hE1S_pos) (by linarith)
      linarith
    have hden1 : 0 < e1 P - probS P P.p1 * ((P.R0 - P.K) / P.R0) * (e1S P - e2S P) := by
      have : 0 ≤ probS P P.p1 * ((P.R0 - P.K) / P.R0) * e2S P :=
        mul_nonneg (mul_nonneg hq0.le hc0.le) hE2S0
      linarith
    have hnum2 : 0 < P.R0 - probS P P.p1 * (P.R0 - P.K) := by
      linarith [mul_le_mul_of_nonneg_right hq1 (by linarith : (0:ℝ) ≤ P.R0 - P.K)]
    have hT2 : 0 < T2 P := by unfold T2; exact div_pos hnum2 hden2
    have hT2eq : T2 P * (e1 P - probS P P.p1 * e1S P * ((P.R0 - P.K) / P.R0))
        = P.R0 - probS P P.p1 * (P.R0 - P.K) := by
      unfold T2; exact div_mul_cancel₀ _ hden2.ne'
    have hT1 : 0 < T1 P := by unfold T1; exact div_pos hR0 hden1
    have hT1eq : T1 P * (e1 P - probS P P.p1 * ((P.R0 - P.K) / P.R0) * (e1S P - e2S P))
        = P.R0 := by
      unfold T1; exact div_mul_cancel₀ _ hden1.ne'
    have hA0pos : 0 < alpha0 P := by unfold alpha0; split_ifs <;> assumption
    have hfacts : P.R0 ≤ alpha0 P * e1 P ∧ alpha0 P * e2 P ≤ P.R0 ∧
        probS P P.p1 * ((P.R0 - P.K) / P.R0 * alpha0 P * e1S P
          - max ((P.R0 - P.K) / P.R0 * alpha0 P * e2S P) (P.R0 - P.K))
          ≤ alpha0 P * e1 P - P.R0 := by
      unfold alpha0
      split_ifs with hcase
      · have hb : e2S P * T2 P ≤ P.R0 := (le_div_iff₀ hT2).1 hcase
        have hx : (T2 P * e1 P - P.R0) * (1 - probS P P.p1 * ((P.R0 - P.K) / P.R0))
            = probS P P.p1 * ((P.R0 - P.K) / P.R0) * (T2 P * (e1S P - e1 P)) := by
          linear_combination hT2eq + (probS P P.p1) * hcR
        have hge : P.R0 ≤ T2 P * e1 P := by
          by_contra hneg; push Not at hneg
          have h1 := mul_neg_of_neg_of_pos (sub_neg.2 hneg) (sub_pos.2 hqc)
          have h2 := mul_nonneg (mul_nonneg hq0.le hc0.le)
            (mul_nonneg hT2.le (sub_nonneg.2 hE1le))
          linarith
        refine ⟨hge, ?_, ?_⟩
        · have := mul_le_mul_of_nonneg_left hE2le hT2.le
          linarith
        · have hmx : (P.R0 - P.K) / P.R0 * T2 P * e2S P ≤ P.R0 - P.K := by
            have := mul_le_mul_of_nonneg_left hb hc0.le
            linarith
          rw [max_eq_right hmx]
          exact le_of_eq (by linear_combination (-1 : ℝ) * hT2eq)
      · refine ⟨?_, ?_, ?_⟩
        · linarith [mul_nonneg (mul_nonneg hT1.le (mul_nonneg hq0.le hc0.le))
            (sub_nonneg.2 hE1S_E2S)]
        · have h' : probS P P.p1 * ((P.R0 - P.K) / P.R0) * (e1S P - e2S P)
              ≤ e1 P - e2 P := by
            linarith [mul_nonneg (sub_nonneg.2 hc1.le)
              (mul_nonneg hq0.le (sub_nonneg.2 hE1S_E2S))]
          have := mul_nonneg hT1.le (by linarith : (0:ℝ) ≤ e1 P - e2 P
            - probS P P.p1 * ((P.R0 - P.K) / P.R0) * (e1S P - e2S P))
          linarith
        · have := mul_le_mul_of_nonneg_left
            (sub_le_sub_left (le_max_left ((P.R0 - P.K) / P.R0 * T1 P * e2S P) (P.R0 - P.K))
              ((P.R0 - P.K) / P.R0 * T1 P * e1S P)) hq0.le
          linarith
    exact ⟨hfacts.1, cf6_delta P (alpha0 P) hβ0 hβ1 hq0.le hq1 hc0.le hc1.le hcR hfacts.1
      hfacts.2.1 (mul_le_mul_of_nonneg_left hE1le hA0pos.le) hsum hfacts.2.2⟩
  have hNoCF : P.R0 ≤ e1 P → invLevelNoCF P (P.R0 / e1 P) = P.R0 := by
    intro h
    have he : 0 < e1 P := by linarith
    unfold invLevelNoCF
    have h1 : P.R0 / e1 P * e1 P = P.R0 := div_mul_cancel₀ _ he.ne'
    have h2 : P.R0 / e1 P * e2 P ≤ P.R0 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ he]
      exact mul_le_mul_of_nonneg_left hE21 hR0.le
    rw [h1, cf6_kappa_eq le_rfl h2]; ring
  have hαS : alphaS P (P.R0 / e1S P) = (P.R0 - P.K) / e1S P := by
    unfold alphaS; field_simp
  have hαS1 : alphaS P (P.R0 / e1S P) * e1S P = P.R0 - P.K := by
    rw [hαS]; exact div_mul_cancel₀ _ hE1S_pos.ne'
  have hαS2 : alphaS P (P.R0 / e1S P) * e2S P ≤ P.R0 - P.K := by
    rw [hαS, div_mul_eq_mul_div, div_le_iff₀ hE1S_pos]
    exact mul_le_mul_of_nonneg_left hE1S_E2S (by linarith)
  have hκS : kappa P.β (alphaS P (P.R0 / e1S P) * e1S P) (alphaS P (P.R0 / e1S P) * e2S P)
      (P.R0 - P.K) = P.R0 - P.K := by
    rw [cf6_kappa_eq (le_of_eq hαS1.symm) hαS2, hαS1]; ring
  refine ⟨?_, ?_, ?_⟩
  · intro hρpos hp1lt hR0e1 hdA
    have hαC : alphaC P = P.R0 / e1S P := by unfold alphaC; rw [if_neg (not_le.mpr hdA)]
    rw [hαC, hNoCF hR0e1]
    have hlt : e1 P < e1S P := by
      have hsp : P.p1 < postS P P.p1 := by
        by_contra hc; push Not at hc
        have := mul_nonneg hD1.le (sub_nonneg.2 hc)
        linarith [mul_pos (mul_pos hρpos hp1pos) (sub_pos.2 hp1lt)]
      rw [he1, he1S]; linarith [mul_lt_mul_of_pos_right hsp hd]
    have hnot : ¬ investsAt0 P (P.R0 / e1S P) := by
      intro h
      have h1 := h.1
      rw [div_mul_eq_mul_div, le_div_iff₀ hE1S_pos] at h1
      linarith [mul_lt_mul_of_pos_left hlt hR0]
    have hF : P.R0 / e1S P * e1F P < P.R0 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hE1S_pos]
      linarith [mul_lt_mul_of_pos_left (lt_of_le_of_lt hE1Fle hlt) hR0]
    unfold invLevelCF
    rw [if_neg hnot, hh, hκS, cf6_kappa_zero hF]
    linarith
  · intro hR0e1 hdA
    have hαC : alphaC P = alpha0 P := by unfold alphaC; rw [if_pos hdA]
    rw [hαC, hNoCF hR0e1]
    unfold invLevelCF
    rw [if_pos (show investsAt0 P (alpha0 P) from hInv)]
    exact cf6_kappa_ge hβ0 hβ1.le hInv.1
  · intro he1lt
    refine ⟨fun α hα0 hα1 => ?_, ?_⟩
    · unfold invLevelNoCF
      apply cf6_kappa_zero
      linarith [mul_le_mul_of_nonneg_right hα1 hE1nn]
    · unfold alphaC
      split_ifs with hdA
      · unfold invLevelCF
        rw [if_pos (show investsAt0 P (alpha0 P) from hInv)]
        linarith [cf6_kappa_ge (v2 := alpha0 P * e2 P) hβ0 hβ1.le hInv.1]
      · unfold invLevelCF
        split_ifs with hinv
        · linarith [cf6_kappa_ge (v2 := P.R0 / e1S P * e2 P) hβ0 hβ1.le hinv.1]
        · rw [hh, hκS]
          have := cf6_kappa_nonneg (v1 := P.R0 / e1S P * e1F P) (v2 := P.R0 / e1S P * e2F P)
            hβ0 hβ1.le hR0.le
          linarith

end CrowdfundVC.Effects


-- Platform entry point: restates the target verbatim.
namespace CrowdfundVC.Effects

/-- Proposition 6 (p. 21). If `e1 ≥ R0` and `Δa > 0` (and the signal is informative, `ρ > 0`, and
`p1 < 1`), the crowdfunding option strictly reduces the expected VC investment level; if `e1 ≥ R0`
and `Δa ≤ 0`, it (weakly) raises it; if `e1 < R0`, there is no investment
without crowdfunding at any share in `[0, 1]`, and the expected level with crowdfunding is
positive. Without crowdfunding the startup offers `αᵒ = R0/e1` (Proposition 1), with crowdfunding `αᶜ`
(Proposition 4). -/
theorem _root_.solution (P : Params)
    (hRf0 : 0 ≤ P.Rf) (hRfR0 : P.Rf < P.R0) (hR0Rs : P.R0 < P.Rs) (hK0 : 0 < P.K)
    (hKR0 : P.K < P.R0) (hρ0 : 0 ≤ P.ρ) (hρ1 : P.ρ ≤ 1) (hβ0 : 0 ≤ P.β) (hβ1 : P.β < 1)
    (hp2 : 0 ≤ P.p2) (hp12 : P.p2 ≤ P.p1) (hp1 : P.p1 ≤ 1) (hpa0 : 0 ≤ P.pa) (hpa1 : P.pa ≤ 1)
    (hea : 0 < ea P) (hI : P.R0 ≤ e1S P) :
    (0 < P.ρ → P.p1 < 1 →
      P.R0 ≤ e1 P → 0 < deltaA P → invLevelCF P (alphaC P) < invLevelNoCF P (P.R0 / e1 P)) ∧
    (P.R0 ≤ e1 P → deltaA P ≤ 0 → invLevelNoCF P (P.R0 / e1 P) ≤ invLevelCF P (alphaC P)) ∧
    (e1 P < P.R0 →
      (∀ α : ℝ, 0 ≤ α → α ≤ 1 → invLevelNoCF P α = 0) ∧ 0 < invLevelCF P (alphaC P)) := by
  apply @CrowdfundVC.Effects.proposition6 <;> assumption

end CrowdfundVC.Effects
