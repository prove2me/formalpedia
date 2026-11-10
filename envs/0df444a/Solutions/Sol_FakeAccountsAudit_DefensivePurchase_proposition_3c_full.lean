-- Prove2me | solution 1 for FakeAccountsAudit.DefensivePurchase.proposition_3c_full
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-09T13:51:34.805482+00:00
-- url     : https://prove2.me/submissions/bd456aad-7bed-4d58-bd5d-341ae6c4eddc

import Mathlib
import Definitions.Def_FakeAccounts_Defensive_Setting
set_option autoImplicit false

namespace P3cHelp1090

open FakeAccounts.Platform FakeAccounts.Defensive

noncomputable def Aq (P : Params) : ℝ := P.lamI * P.mu * (1 - P.l ^ 2)
noncomputable def Kq (P : Params) : ℝ := P.c1 * (1 - P.tau) ^ 2
noncomputable def Bq (P : Params) : ℝ := P.c0 - Kq P * P.p0
noncomputable def Dq (P : Params) : ℝ := 1 / P.qL - 1 / P.qH
noncomputable def Gq (P : Params) (u v : ℝ) : ℝ := Bq P * Aq P + Kq P * P.l * u * v

lemma x_formula (P : Params) (hqL : P.qL ≠ 0) (hqH : P.qH ≠ 0) (hs : 1 - P.tau ≠ 0)
    (d : ℝ) (hu : price P d ≠ 0) :
    xCsepH P d = Dq P * (Bq P * Aq P / price P d - Bq P * P.l + Kq P * Aq P
      - Kq P * P.l * price P d) := by
  have hd : d = (1 - P.tau) * (price P d - P.p0) := by
    unfold price; field_simp; ring
  unfold xCsepH nCsep2 nUnSep nIn cost Dq Bq Aq Kq
  generalize price P d = u at hd hu ⊢
  subst hd
  field_simp
  ring

lemma x_sub (P : Params) (hqL : P.qL ≠ 0) (hqH : P.qH ≠ 0) (hs : 1 - P.tau ≠ 0)
    (d e : ℝ) (hu : 0 < price P d) (hv : 0 < price P e) :
    xCsepH P d - xCsepH P e
      = Dq P * (price P e - price P d) * Gq P (price P d) (price P e)
          / (price P d * price P e) := by
  rw [x_formula P hqL hqH hs d hu.ne', x_formula P hqL hqH hs e hv.ne']
  unfold Gq
  generalize price P d = u at hu ⊢
  generalize price P e = v at hv ⊢
  field_simp
  ring

lemma price_pos (P : Params) (hp0 : 0 < P.p0) (htau : P.tau < 1) (d : ℝ) (hd : 0 ≤ d) :
    0 < price P d := by
  unfold price
  have := div_nonneg hd (sub_pos.2 htau).le
  linarith

lemma p0_le_price (P : Params) (htau : P.tau < 1) (d : ℝ) (hd : 0 ≤ d) :
    P.p0 ≤ price P d := by
  unfold price
  have := div_nonneg hd (sub_pos.2 htau).le
  linarith

lemma price_lt (P : Params) (htau : P.tau < 1) (d e : ℝ) (hde : d < e) :
    price P d < price P e := by
  unfold price
  have hs : 0 < 1 - P.tau := sub_pos.2 htau
  have : d / (1 - P.tau) < e / (1 - P.tau) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_lt_mul_of_pos_right hde (inv_pos.2 hs)
  linarith

lemma price_le (P : Params) (htau : P.tau < 1) (d e : ℝ) (hde : d ≤ e) :
    price P d ≤ price P e := by
  unfold price
  have hs : 0 < 1 - P.tau := sub_pos.2 htau
  have : d / (1 - P.tau) ≤ e / (1 - P.tau) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hde (inv_nonneg.2 hs.le)
  linarith

lemma Dq_pos (P : Params) (hqL : 0 < P.qL) (hq : P.qL < P.qH) : 0 < Dq P := by
  unfold Dq
  exact sub_pos.2 (one_div_lt_one_div_of_lt hqL hq)

lemma x_lt_of_G_pos (P : Params) (hqL : 0 < P.qL) (hq : P.qL < P.qH)
    (hp0 : 0 < P.p0) (htau : P.tau < 1) (d e : ℝ) (hd : 0 ≤ d) (hde : d < e)
    (hG : 0 < Gq P (price P d) (price P e)) : xCsepH P e < xCsepH P d := by
  have hu := price_pos P hp0 htau d hd
  have hv := price_pos P hp0 htau e (by linarith)
  have hsub := x_sub P hqL.ne' (by linarith : (0:ℝ) < P.qH).ne' (sub_pos.2 htau).ne' d e hu hv
  have hD := Dq_pos P hqL hq
  have hp := price_lt P htau d e hde
  have : 0 < xCsepH P d - xCsepH P e := by
    rw [hsub]
    exact div_pos (mul_pos (mul_pos hD (sub_pos.2 hp)) hG) (mul_pos hu hv)
  linarith

lemma x_le_of_G_nonneg (P : Params) (hqL : 0 < P.qL) (hq : P.qL < P.qH)
    (hp0 : 0 < P.p0) (htau : P.tau < 1) (d e : ℝ) (hd : 0 ≤ d) (hde : d < e)
    (hG : 0 ≤ Gq P (price P d) (price P e)) : xCsepH P e ≤ xCsepH P d := by
  have hu := price_pos P hp0 htau d hd
  have hv := price_pos P hp0 htau e (by linarith)
  have hsub := x_sub P hqL.ne' (by linarith : (0:ℝ) < P.qH).ne' (sub_pos.2 htau).ne' d e hu hv
  have hD := Dq_pos P hqL hq
  have hp := price_lt P htau d e hde
  have : 0 ≤ xCsepH P d - xCsepH P e := by
    rw [hsub]
    exact div_nonneg (mul_nonneg (mul_nonneg hD.le (sub_pos.2 hp).le) hG) (mul_pos hu hv).le
  linarith

lemma x_lt_of_G_neg (P : Params) (hqL : 0 < P.qL) (hq : P.qL < P.qH)
    (hp0 : 0 < P.p0) (htau : P.tau < 1) (d e : ℝ) (hd : 0 ≤ d) (hde : d < e)
    (hG : Gq P (price P d) (price P e) < 0) : xCsepH P d < xCsepH P e := by
  have hu := price_pos P hp0 htau d hd
  have hv := price_pos P hp0 htau e (by linarith)
  have hsub := x_sub P hqL.ne' (by linarith : (0:ℝ) < P.qH).ne' (sub_pos.2 htau).ne' d e hu hv
  have hD := Dq_pos P hqL hq
  have hp := price_lt P htau d e hde
  have : xCsepH P d - xCsepH P e < 0 := by
    rw [hsub]
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (mul_pos hD (sub_pos.2 hp)) hG)
      (mul_pos hu hv)
  linarith

set_option maxHeartbeats 1000000 in
theorem main (P : Params)
    (hmu : 0 < P.mu) (hlamI : 0 < P.lamI)
    (hl : 0 < P.l) (hl_one : P.l < 1)
    (hqL : 0 < P.qL) (hq : P.qL < P.qH)
    (hc0 : 0 ≤ P.c0) (hc1 : 0 ≤ P.c1)
    (htau_one : P.tau < 1)
    (hp0 : 0 < P.p0) (hA3 : P.p0 < eta2 P) :
    (P.c1 * (1 - P.tau) ^ 2 ≤
        P.lamI * P.mu * (1 - P.l ^ 2) * P.c0 /
          (P.p0 * (P.lamI * P.mu * (1 - P.l ^ 2) - P.p0 * P.l)) →
      AntitoneOn (xCsepH P) (Set.Icc 0 (d2 P)) ∧
        (0 < P.c0 + P.c1 →
          StrictAntiOn (xCsepH P) (Set.Icc 0 (d2 P)))) ∧
    (P.c0 = 0 → P.c1 = 0 →
      ∀ d ∈ Set.Icc 0 (d2 P), xCsepH P d = 0) ∧
    (P.lamI * P.mu * (1 - P.l ^ 2) * P.c0 /
        (P.p0 * (P.lamI * P.mu * (1 - P.l ^ 2) - P.p0 * P.l)) <
          P.c1 * (1 - P.tau) ^ 2 →
      ∃ h : ℝ, 0 < h ∧ h < d2 P ∧
        StrictMonoOn (xCsepH P) (Set.Icc 0 h) ∧
        StrictAntiOn (xCsepH P) (Set.Icc h (d2 P))) := by
  have hs : 0 < 1 - P.tau := sub_pos.2 htau_one
  have hl2 : P.l ^ 2 < 1 := by nlinarith
  have hA : 0 < Aq P := by
    unfold Aq; exact mul_pos (mul_pos hlamI hmu) (by linarith)
  have he : eta2 P * P.l = Aq P := by
    unfold eta2 Aq; field_simp
  have hAl : P.p0 * P.l < Aq P := by
    rw [← he]; exact mul_lt_mul_of_pos_right hA3 hl
  have hK : 0 ≤ Kq P := by unfold Kq; positivity
  have hden : 0 < P.p0 * (Aq P - P.p0 * P.l) := mul_pos hp0 (by linarith)
  have hTdef : P.lamI * P.mu * (1 - P.l ^ 2) * P.c0 /
      (P.p0 * (P.lamI * P.mu * (1 - P.l ^ 2) - P.p0 * P.l))
        = Aq P * P.c0 / (P.p0 * (Aq P - P.p0 * P.l)) := rfl
  have hKdef : P.c1 * (1 - P.tau) ^ 2 = Kq P := rfl
  rw [hTdef, hKdef]
  refine ⟨?_, ?_, ?_⟩
  · intro h22
    rw [le_div_iff₀ hden] at h22
    have hg0 : 0 ≤ Bq P * Aq P + Kq P * P.l * (P.p0 * P.p0) := by
      unfold Bq; linarith
    -- G is at least its corner value
    have hGge : ∀ a b : ℝ, 0 ≤ a → a < b →
        P.p0 * P.p0 ≤ price P a * price P b := by
      intro a b ha hab
      have hpa := p0_le_price P htau_one a ha
      have hpb := p0_le_price P htau_one b (by linarith)
      exact mul_le_mul hpa hpb hp0.le (by linarith)
    refine ⟨?_, ?_⟩
    · intro a ha b hb hab
      rcases eq_or_lt_of_le hab with h | h
      · rw [h]
      · apply x_le_of_G_nonneg P hqL hq hp0 htau_one a b ha.1 h
        have hpp := hGge a b ha.1 h
        have := mul_le_mul_of_nonneg_left hpp (mul_nonneg hK hl.le)
        unfold Gq
        linarith
    · intro hcc a ha b hb hab
      apply x_lt_of_G_pos P hqL hq hp0 htau_one a b ha.1 hab
      rcases hc1.lt_or_eq with h1 | h1
      · have hKpos : 0 < Kq P := by unfold Kq; positivity
        have hpa := p0_le_price P htau_one a ha.1
        have hpb : P.p0 < price P b := by
          have := price_lt P htau_one a b hab
          linarith
        have hpapos := price_pos P hp0 htau_one a ha.1
        have hpp : P.p0 * P.p0 < price P a * price P b :=
          mul_lt_mul' hpa hpb hp0.le hpapos
        have := mul_lt_mul_of_pos_left hpp (mul_pos hKpos hl)
        unfold Gq
        linarith
      · have hK0 : Kq P = 0 := by unfold Kq; rw [← h1]; ring
        have hc0pos : 0 < P.c0 := by linarith
        have := mul_pos hc0pos hA
        unfold Gq Bq
        rw [hK0]
        linarith
  · intro h0 h1 d _
    unfold xCsepH nCsep2 nUnSep nIn cost
    rw [h0, h1]
    simp
  · intro hT
    rw [div_lt_iff₀ hden] at hT
    have hKpos : 0 < Kq P := by
      rcases hK.lt_or_eq with h | h
      · exact h
      · rw [← h] at hT
        linarith [mul_nonneg hA.le hc0]
    have hKl : 0 < Kq P * P.l := mul_pos hKpos hl
    have hg0 : Bq P * Aq P + Kq P * P.l * (P.p0 * P.p0) < 0 := by
      unfold Bq; linarith
    set N : ℝ := -(Bq P * Aq P) / (Kq P * P.l) with hNdef
    have hN : P.p0 ^ 2 < N := by
      rw [hNdef, lt_div_iff₀ hKl]; linarith
    have hN0 : 0 ≤ N := by linarith [sq_nonneg P.p0]
    set us : ℝ := Real.sqrt N with husdef
    have hus_gt : P.p0 < us := (Real.lt_sqrt hp0.le).2 hN
    have hus_pos : 0 < us := by linarith
    have hus_sq : us ^ 2 = N := Real.sq_sqrt hN0
    have hKus : Kq P * P.l * (us * us) = -(Bq P * Aq P) := by
      rw [← sq, hus_sq, hNdef]
      field_simp
    have heta_pos : 0 < eta2 P := by linarith
    have hus_lt : us < eta2 P := by
      rw [husdef, Real.sqrt_lt' heta_pos, hNdef, div_lt_iff₀ hKl]
      have h1 : eta2 P ^ 2 * (Kq P * P.l) = Kq P * Aq P * eta2 P := by
        rw [← he]; ring
      have h2 := mul_lt_mul_of_pos_left hA3 (mul_pos hKpos hA)
      have h3 := mul_nonneg hc0 hA.le
      rw [h1]
      unfold Bq
      linarith
    refine ⟨(1 - P.tau) * (us - P.p0), mul_pos hs (by linarith), ?_, ?_, ?_⟩
    · unfold d2
      exact mul_lt_mul_of_pos_left (by linarith) hs
    · have hph : price P ((1 - P.tau) * (us - P.p0)) = us := by
        unfold price; field_simp; ring
      intro a ha b hb hab
      apply x_lt_of_G_neg P hqL hq hp0 htau_one a b ha.1 hab
      have hpa := price_pos P hp0 htau_one a ha.1
      have hpab := price_lt P htau_one a b hab
      have hpb : price P b ≤ us := by
        rw [← hph]; exact price_le P htau_one b _ hb.2
      have h1 : price P a * price P b ≤ price P a * us :=
        mul_le_mul_of_nonneg_left hpb hpa.le
      have h2 : price P a * us < us * us :=
        mul_lt_mul_of_pos_right (by linarith) hus_pos
      have h3 := mul_lt_mul_of_pos_left (lt_of_le_of_lt h1 h2) hKl
      unfold Gq
      linarith
    · have hph : price P ((1 - P.tau) * (us - P.p0)) = us := by
        unfold price; field_simp; ring
      have hh0 : 0 < (1 - P.tau) * (us - P.p0) := mul_pos hs (by linarith)
      intro a ha b hb hab
      have ha0 : 0 ≤ a := by linarith [ha.1]
      apply x_lt_of_G_pos P hqL hq hp0 htau_one a b ha0 hab
      have hpa : us ≤ price P a := by
        rw [← hph]; exact price_le P htau_one _ a ha.1
      have hpab := price_lt P htau_one a b hab
      have hpapos := price_pos P hp0 htau_one a ha0
      have hpp : us * us < price P a * price P b :=
        mul_lt_mul' hpa (by linarith) hus_pos.le hpapos
      have h3 := mul_lt_mul_of_pos_left hpp hKl
      unfold Gq
      linarith

end P3cHelp1090

theorem solution (P : FakeAccounts.Platform.Params)
    (hmu : 0 < P.mu) (hlamI : 0 < P.lamI) (hlamI_one : P.lamI < 1)
    (hl : 0 < P.l) (hl_one : P.l < 1)
    (hqL : 0 < P.qL) (hq : P.qL < P.qH)
    (hc0 : 0 ≤ P.c0) (hc1 : 0 ≤ P.c1)
    (htau : 0 ≤ P.tau) (htau_one : P.tau < 1)
    (hp0 : 0 < P.p0) (hA3 : P.p0 < FakeAccounts.Platform.eta2 P) :
    (P.c1 * (1 - P.tau) ^ 2 ≤
        P.lamI * P.mu * (1 - P.l ^ 2) * P.c0 /
          (P.p0 * (P.lamI * P.mu * (1 - P.l ^ 2) - P.p0 * P.l)) →
      AntitoneOn (FakeAccounts.Defensive.xCsepH P) (Set.Icc 0 (FakeAccounts.Platform.d2 P)) ∧
        (0 < P.c0 + P.c1 →
          StrictAntiOn (FakeAccounts.Defensive.xCsepH P)
            (Set.Icc 0 (FakeAccounts.Platform.d2 P)))) ∧
    (P.c0 = 0 → P.c1 = 0 →
      ∀ d ∈ Set.Icc 0 (FakeAccounts.Platform.d2 P),
        FakeAccounts.Defensive.xCsepH P d = 0) ∧
    (P.lamI * P.mu * (1 - P.l ^ 2) * P.c0 /
        (P.p0 * (P.lamI * P.mu * (1 - P.l ^ 2) - P.p0 * P.l)) <
          P.c1 * (1 - P.tau) ^ 2 →
      ∃ h : ℝ, 0 < h ∧ h < FakeAccounts.Platform.d2 P ∧
        StrictMonoOn (FakeAccounts.Defensive.xCsepH P) (Set.Icc 0 h) ∧
        StrictAntiOn (FakeAccounts.Defensive.xCsepH P)
          (Set.Icc h (FakeAccounts.Platform.d2 P))) := by
  exact P3cHelp1090.main P hmu hlamI hl hl_one hqL hq hc0 hc1 htau_one hp0 hA3
