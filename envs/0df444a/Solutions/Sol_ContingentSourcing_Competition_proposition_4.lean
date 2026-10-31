-- Prove2me | solution 1 for ContingentSourcing.Competition.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T07:07:03.762991+00:00
-- url     : https://prove2.me/submissions/3a1a76f5-e647-4ed0-8017-202cf7b9e50d

import Mathlib
import Definitions.Def_ContingentSourcing_Competition_Model
import Theorems.Thm_ContingentSourcing_Competition_proposition_2_i_corrected_v2
import Theorems.Thm_ContingentSourcing_Competition_proposition_3_i_ii_corrected

open ContingentSourcing.Competition

namespace CSProp4Aux

lemma PB1 (P : Params) : P.PB 1 = 1 - P.P1 := by simp [Params.PB, Params.P0]
lemma PG1 (P : Params) : P.PG 1 = P.P1 := by simp [Params.PG, Params.P0]
lemma P0G1 (P : Params) : P.P0G 1 = 0 := by simp [Params.P0G]
lemma P1G1 (P : Params) (h : 0 < P.P1) : P.P1G 1 = 1 := by
  simp [Params.P1G, PG1, h.ne']
lemma PB0 (P : Params) : P.PB 0 = 0 := by simp [Params.PB]
lemma PG0 (P : Params) : P.PG 0 = 1 := by simp [Params.PG]
lemma P0G0 (P : Params) : P.P0G 0 = 1 - P.P1 := by simp [Params.P0G, Params.PG, Params.P0]
lemma P1G0 (P : Params) : P.P1G 0 = P.P1 := by simp [Params.P1G, Params.PG]

/-- revenue bound: R(x) - c x ≤ (m-c)²/4 for 0 ≤ c, x ≥ 0. -/
lemma rev_le (P : Params) (c x : ℝ) (hc : 0 ≤ c) (hx : 0 ≤ x) :
    P.revenue x - c * x ≤ (P.m - c) ^ 2 / 4 := by
  unfold Params.revenue
  split_ifs with h
  · nlinarith [sq_nonneg (2 * x - (P.m - c))]
  · push_neg at h; nlinarith [sq_nonneg c]

lemma rev_le0 (P : Params) (c x : ℝ) (hm : 0 < P.m) (hc : P.m ≤ c) (hx : 0 ≤ x) :
    P.revenue x - c * x ≤ 0 := by
  unfold Params.revenue
  split_ifs with h
  · nlinarith
  · push_neg at h; nlinarith

lemma rev_at (P : Params) (c : ℝ) (hc : 0 ≤ c) :
    P.revenue ((P.m - c) / 2) - c * ((P.m - c) / 2) = (P.m - c) ^ 2 / 4 := by
  unfold Params.revenue
  rw [if_pos (by linarith)]; ring

lemma rev_zero (P : Params) (hm : 0 ≤ P.m) : P.revenue 0 = 0 := by
  unfold Params.revenue; rw [if_pos (by linarith)]; ring

lemma bv_eq (P : Params) (ρ : ℝ) (w : Prices) (q0 : Orders) (V : ℝ) (hq0 : q0.Feasible)
    (hV : P.buyerProfit ρ w q0 = V) (hle : ∀ q : Orders, q.Feasible → P.buyerProfit ρ w q ≤ V) :
    P.buyerValue ρ w = V := by
  unfold Params.buyerValue
  apply IsGreatest.csSup_eq
  refine ⟨⟨q0, hq0, hV.symm⟩, ?_⟩
  rintro v ⟨q, hq, rfl⟩
  exact hle q hq

lemma bv1 (P : Params) (hP : P.Standing) (w : Prices) (hwU0 : 0 ≤ w.wU) (hwUm : w.wU ≤ P.m)
    (hwEm : w.wE ≤ P.m) (hUE : w.wU ≤ w.wE)
    (hR : P.P1 * w.wU + (1 - P.P1) * w.wE ≤ w.wR) :
    P.buyerValue 1 w = (1 - P.P1) * (P.m - w.wE) ^ 2 / 4 + P.P1 * (P.m - w.wU) ^ 2 / 4 := by
  obtain ⟨hm, hp0, hp1, -, -, -, -⟩ := hP
  apply bv_eq P 1 w ⟨(P.m - w.wU) / 2, 0, 0, (P.m - w.wE) / 2⟩
  · refine ⟨by linarith, le_refl _, le_refl _, by linarith⟩
  · simp only [Params.buyerProfit, PB1, PG1, P0G1, P1G1 P hp0]
    have e1 := rev_at P w.wE (by linarith)
    have e2 := rev_at P w.wU hwU0
    simp only [zero_add, add_zero] at *
    nlinarith [e1, e2]
  · rintro ⟨QU, QR, QEG, QEB⟩ ⟨h1, h2, h3, h4⟩
    simp only [Params.buyerProfit, PB1, PG1, P0G1, P1G1 P hp0]
    have r1 := rev_le P w.wE (QR + QEB) (by linarith) (by linarith)
    have r2 := rev_le P w.wU (QU + QR + QEG) hwU0 (by linarith)
    have a1 := mul_le_mul_of_nonneg_left r1 (by linarith : (0:ℝ) ≤ 1 - P.P1)
    have a2 := mul_le_mul_of_nonneg_left r2 hp0.le
    have a3 := mul_nonneg h2 (by linarith : (0:ℝ) ≤ w.wR - (P.P1 * w.wU + (1 - P.P1) * w.wE))
    have a4 := mul_nonneg hp0.le (mul_nonneg h3 (by linarith : (0:ℝ) ≤ w.wE - w.wU))
    nlinarith [a1, a2, a3, a4]

/-- ρ = 0, case where R gets part of the initial order. -/
lemma bv0a (P : Params) (hP : P.Standing) (w : Prices) (hwU0 : 0 ≤ w.wU) (hUR : w.wU ≤ w.wR)
    (hRE : w.wR ≤ w.wE) (hR : w.wR ≤ P.P1 * w.wU + (1 - P.P1) * P.m) :
    P.buyerValue 0 w = (1 - P.P1) * (P.m - (w.wR - P.P1 * w.wU) / (1 - P.P1)) ^ 2 / 4
        + P.P1 * (P.m - w.wU) ^ 2 / 4 := by
  obtain ⟨hm, hp0, hp1, -, -, -, -⟩ := hP
  have hq : 0 < 1 - P.P1 := by linarith
  set c := (w.wR - P.P1 * w.wU) / (1 - P.P1) with hc
  have hcR : w.wR = P.P1 * w.wU + (1 - P.P1) * c := by rw [hc]; field_simp; ring
  have hc0 : w.wU ≤ c := by
    by_contra hh; push_neg at hh; nlinarith
  have hcm : c ≤ P.m := by
    by_contra hh; push_neg at hh; nlinarith
  apply bv_eq P 0 w ⟨(c - w.wU) / 2, (P.m - c) / 2, 0, 0⟩
  · refine ⟨by linarith, by linarith, le_refl _, le_refl _⟩
  · simp only [Params.buyerProfit, PB0, PG0, P0G0, P1G0]
    have e1 := rev_at P c (by linarith)
    have e2 := rev_at P w.wU hwU0
    have : (c - w.wU) / 2 + (P.m - c) / 2 + 0 = (P.m - w.wU) / 2 := by ring
    rw [this]
    simp only [add_zero]
    rw [hcR]
    nlinarith [e1, e2]
  · rintro ⟨QU, QR, QEG, QEB⟩ ⟨h1, h2, h3, h4⟩
    simp only [Params.buyerProfit, PB0, PG0, P0G0, P1G0]
    have r1 := rev_le P c (QR + QEG) (by linarith) (by linarith)
    have r2 := rev_le P w.wU (QU + QR + QEG) hwU0 (by linarith)
    have a1 := mul_le_mul_of_nonneg_left r1 hq.le
    have a2 := mul_le_mul_of_nonneg_left r2 hp0.le
    have a3 := mul_nonneg h3 (by linarith : (0:ℝ) ≤ w.wE - w.wR)
    rw [hcR] at *
    nlinarith [a1, a2, a3]

/-- ρ = 0, case where R gets no initial order. -/
lemma bv0b (P : Params) (hP : P.Standing) (w : Prices) (hwU0 : 0 ≤ w.wU) (hUR : w.wU ≤ w.wR)
    (hRE : w.wR ≤ w.wE) (hwUm : w.wU ≤ P.m) (hR : P.P1 * w.wU + (1 - P.P1) * P.m ≤ w.wR) :
    P.buyerValue 0 w = P.P1 * (P.m - w.wU) ^ 2 / 4 := by
  obtain ⟨hm, hp0, hp1, -, -, -, -⟩ := hP
  have hq : 0 < 1 - P.P1 := by linarith
  apply bv_eq P 0 w ⟨(P.m - w.wU) / 2, 0, 0, 0⟩
  · refine ⟨by linarith, le_refl _, le_refl _, le_refl _⟩
  · simp only [Params.buyerProfit, PB0, PG0, P0G0, P1G0]
    have e2 := rev_at P w.wU hwU0
    simp only [add_zero, zero_add, rev_zero P hm.le]
    nlinarith [e2]
  · rintro ⟨QU, QR, QEG, QEB⟩ ⟨h1, h2, h3, h4⟩
    simp only [Params.buyerProfit, PB0, PG0, P0G0, P1G0]
    have r1 := rev_le0 P P.m (QR + QEG) hm le_rfl (by linarith)
    have r2 := rev_le P w.wU (QU + QR + QEG) hwU0 (by linarith)
    have a1 := mul_le_mul_of_nonneg_left r1 hq.le
    have a2 := mul_le_mul_of_nonneg_left r2 hp0.le
    have a3 := mul_nonneg h3 (by linarith : (0:ℝ) ≤ w.wE - w.wR)
    have a5 := mul_nonneg (add_nonneg h2 h3)
      (by linarith : (0:ℝ) ≤ w.wR - (P.P1 * w.wU + (1 - P.P1) * P.m))
    nlinarith [a1, a2, a3, a5]

lemma order1 (P : Params) (w : Prices) (h : P.Contingent 1 w) : P.order 1 w = P.orderI w := by
  unfold Params.order; rw [if_neg h.1, if_pos h.2]

lemma eta1_one (P : Params) (w : Prices) :
    P.eta1 1 w = P.P1 * w.wU + (1 - P.P1) * w.wE := by
  simp [Params.eta1, PB1, PG1, P0G1]

lemma eta1_zero (P : Params) (w : Prices) :
    P.eta1 0 w = P.P1 * w.wU + (1 - P.P1) * P.m := by
  simp [Params.eta1, PB0, PG0, P0G0]

lemma pay1 (P : Params) (w : Prices) (h : P.Contingent 1 w) :
    P.payU 1 w = (P.P1 * w.wU - P.cU) * ((P.m - w.wU) / 2) ∧
    P.payR 1 w = (1 - P.P1) * (w.wE - P.cR) * ((P.m - w.wE) / 2) := by
  unfold Params.payU Params.payR
  rw [order1 P w h]
  simp [Params.orderI, PB1]

lemma order0_i (P : Params) (hP : P.Standing) (w : Prices) (hQR : (P.order 0 w).QR = 0)
    (hQU : 0 < (P.order 0 w).QU) :
    (P.order 0 w).QU = (P.m - w.wU) / 2 ∧ w.wU < w.wR ∧
      P.P1 * w.wU + (1 - P.P1) * P.m ≤ w.wR := by
  obtain ⟨hm, hp0, hp1, -, -, -, -⟩ := hP
  have hq : (1 - P.P1) ≠ 0 := by linarith
  unfold Params.order at *
  split_ifs at * with h1 h2 h3
  · simp [Params.orderIV] at hQU
  · rw [eta1_zero] at h2
    simp only [Params.orderI] at *
    exact ⟨by trivial, by linarith, h2⟩
  · simp only [Params.orderII, PB0, PG0, P0G0, Params.P0] at *
    have : (1 - P.P1) * P.m - w.wR + 0 * w.wE + P.P1 * w.wU = 0 := by
      rcases div_eq_zero_iff.mp hQR with h | h
      · linarith
      · exfalso; simp at h; exact hq (by linarith)
    refine ⟨?_, by push_neg at h1; linarith, by linarith⟩
    field_simp; linarith
  · simp only [Params.orderIII, Params.P0] at *
    have : (1 - P.P1) * P.m - w.wR + P.P1 * w.wU = 0 := by
      rcases div_eq_zero_iff.mp hQR with h | h
      · linarith
      · exfalso; exact hq (by linarith)
    refine ⟨?_, by push_neg at h1; linarith, by linarith⟩
    field_simp; linarith

lemma order0_ii (P : Params) (hP : P.Standing) (w : Prices) (hQR : 0 < (P.order 0 w).QR)
    (hQU : 0 < (P.order 0 w).QU) :
    (P.order 0 w).QU = (w.wR - w.wU) / (2 * (1 - P.P1)) ∧
    (P.order 0 w).QR = ((1 - P.P1) * P.m - w.wR + P.P1 * w.wU) / (2 * (1 - P.P1)) ∧
    w.wU < w.wR ∧ w.wR < P.P1 * w.wU + (1 - P.P1) * P.m := by
  obtain ⟨hm, hp0, hp1, -, -, -, -⟩ := hP
  have hq : (1 - P.P1) ≠ 0 := by linarith
  unfold Params.order at *
  split_ifs at * with h1 h2 h3
  · simp [Params.orderIV] at hQU
  · simp [Params.orderI] at hQR
  · rw [eta1_zero] at h2
    simp only [Params.orderII, PB0, PG0, P0G0, Params.P0] at *
    push_neg at h1 h2
    refine ⟨?_, ?_, h1, h2⟩ <;> ring
  · rw [eta1_zero] at h2
    simp only [Params.orderIII, Params.P0] at *
    push_neg at h1 h2
    exact ⟨trivial, trivial, h1, h2⟩


/-! ### Pure comparisons. Notation: k = p m - cU, x = m - cR. -/

/-- ρ=1 case (i-a) vs ρ=0 case (i-b). -/
lemma cmp_ia_ib (m p cU cR wU1 wU0 : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hx : 0 < m - cR) (hwU1 : wU1 = (p * m + cU) / (2 * p)) (hwU0 : wU0 = (cR - (1 - p) * m) / p) :
    (p * wU1 - cU) * ((p * m - cU) - 2 * (m - cR)) ^ 2 / (8 * p) * 0 = 0 ∧
    (p * wU1 - cU) * ((m - wU1) / 2) - (p * wU0 - cU) * ((m - wU0) / 2)
      = ((p * m - cU) - 2 * (m - cR)) ^ 2 / (8 * p) ∧
    ((1 - p) * (m - (m + cR) / 2) ^ 2 / 4 + p * (m - wU1) ^ 2 / 4) - p * (m - wU0) ^ 2 / 4
      = ((p * m - cU) ^ 2 - (4 - p + p ^ 2) * (m - cR) ^ 2) / (16 * p) ∧
    0 < (1 - p) * ((m + cR) / 2 - cR) * ((m - (m + cR) / 2) / 2) := by
  have hp : p ≠ 0 := hp0.ne'
  subst hwU1 hwU0
  refine ⟨by ring, by field_simp; ring, by field_simp; ring, ?_⟩
  have : (1 - p) * ((m + cR) / 2 - cR) * ((m - (m + cR) / 2) / 2) = (1 - p) * (m - cR) ^ 2 / 8 := by
    ring
  rw [this]; have : 0 < 1 - p := by linarith
  positivity

/-- ρ=1 case (i-b) vs ρ=0 case (i-b). -/
lemma cmp_ib_ib (m p cU cR wU0 : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hx : 0 < m - cR) (hk : 0 < p * m - cU) (h1 : p * m - cU ≤ 2 * p * (m - cR))
    (hwU0 : wU0 = (cR - (1 - p) * m) / p) :
    (p * wU0 - cU) * ((m - wU0) / 2) < (p * cR - cU) * ((m - cR) / 2) ∧
    ((1 - p) * (m - (m + cR) / 2) ^ 2 / 4 + p * (m - cR) ^ 2 / 4) < p * (m - wU0) ^ 2 / 4 := by
  have hp : p ≠ 0 := hp0.ne'
  subst hwU0
  obtain ⟨k, rfl⟩ : ∃ k, cU = p * m - k := ⟨p * m - cU, by ring⟩
  obtain ⟨x, rfl⟩ : ∃ x, cR = m - x := ⟨m - cR, by ring⟩
  have hx' : 0 < x := by linarith
  have hk' : 0 < k := by linarith
  have h1' : k ≤ 2 * p * x := by linarith
  clear hx hk h1
  constructor
  · rw [← sub_pos]
    have e : (p * (m - x) - (p * m - k)) * ((m - (m - x)) / 2) -
        (p * ((m - x - (1 - p) * m) / p) - (p * m - k)) * ((m - (m - x - (1 - p) * m) / p) / 2)
        = x * (1 - p) * ((1 + p) * x - k) / (2 * p) := by field_simp; ring
    rw [e]
    have : 0 < (1 + p) * x - k := by nlinarith
    have : 0 < 1 - p := by linarith
    positivity
  · rw [← sub_pos]
    have e : p * (m - (m - x - (1 - p) * m) / p) ^ 2 / 4 -
        ((1 - p) * (m - (m + (m - x)) / 2) ^ 2 / 4 + p * (m - (m - x)) ^ 2 / 4)
        = x ^ 2 * ((1 - p) * (4 + 3 * p)) / (16 * p) := by field_simp; ring
    rw [e]
    have : 0 < 1 - p := by linarith
    positivity


lemma R_ii (p k x : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hx : 0 < x)
    (h2 : k ≤ (2 - p) * x) (h3 : p * (3 - p) * x < 2 * k) :
    0 < (2 * k - p * (3 - p) * x) * ((p ^ 2 - 7 * p + 8) * x - 2 * k) / (8 * (4 - p) ^ 2 * (1 - p)) := by
  have hq : 0 < 1 - p := by linarith
  have hF : 0 < (p ^ 2 - 7 * p + 8) * x - 2 * k := by
    have : 0 < (1 - p) * (4 - p) * x := by
      have : 0 < 4 - p := by linarith
      positivity
    nlinarith
  have ha3 : 0 < 2 * k - p * (3 - p) * x := by linarith
  have : 0 < 4 - p := by linarith
  positivity

/-- ρ=1 case (i-a) vs ρ=0 case (ii). -/
lemma cmp_ia_ii (m p cU cR wU0 wR0 U0 U1 R0 R1 B0 B1 : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hx : 0 < m - cR) (hk : 0 < p * m - cU)
    (h1 : 2 * p * (m - cR) < p * m - cU) (h2 : p * m - cU ≤ (2 - p) * (m - cR))
    (h3 : p * (3 - p) * (m - cR) < 2 * (p * m - cU))
    (hwU0 : wU0 = ((1 - p) * m + cR + 2 * cU / p) / (3 + (1 - p)))
    (hwR0 : wR0 = (2 * (1 - p) * m + 2 * cR + cU) / (3 + (1 - p)))
    (hU0 : U0 = (p * wU0 - cU) * ((wR0 - wU0) / (2 * (1 - p))))
    (hU1 : U1 = (p * ((p * m + cU) / (2 * p)) - cU) * ((m - (p * m + cU) / (2 * p)) / 2))
    (hR0 : R0 = (wR0 - cR) * (((1 - p) * m - wR0 + p * wU0) / (2 * (1 - p))))
    (hR1 : R1 = (1 - p) * ((m + cR) / 2 - cR) * ((m - (m + cR) / 2) / 2))
    (hB0 : B0 = (1 - p) * (m - (wR0 - p * wU0) / (1 - p)) ^ 2 / 4 + p * (m - wU0) ^ 2 / 4)
    (hB1 : B1 = (1 - p) * (m - (m + cR) / 2) ^ 2 / 4 + p * (m - (p * m + cU) / (2 * p)) ^ 2 / 4) :
    U0 < U1 ∧ R0 < R1 ∧ B1 < B0 := by
  have hp : p ≠ 0 := hp0.ne'
  have hq : 1 - p ≠ 0 := by intro h; linarith
  have hq0 : 0 < 1 - p := by linarith
  have h4 : (3 + (1 - p)) ≠ 0 := by intro h; linarith
  have h4' : (4 - p) ≠ 0 := by intro h; linarith
  subst hwU0 hwR0 hU0 hU1 hR0 hR1 hB0 hB1
  obtain ⟨k, rfl⟩ : ∃ k, cU = p * m - k := ⟨p * m - cU, by ring⟩
  obtain ⟨x, rfl⟩ : ∃ x, cR = m - x := ⟨m - cR, by ring⟩
  have hx' : 0 < x := by linarith
  have hk' : 0 < k := by linarith
  have h1' : 2 * p * x < k := by linarith
  have h2' : k ≤ (2 - p) * x := by linarith
  have h3' : p * (3 - p) * x < 2 * k := by linarith
  clear hx hk h1 h2 h3
  refine ⟨?_, ?_, ?_⟩
  · set NU := (p ^ 2 - 5 * p + 8) * k ^ 2 + (8 * p - 16) * k * x + 4 * p * x ^ 2 with hNU
    have e : (p * ((p * m + (p * m - k)) / (2 * p)) - (p * m - k)) * ((m - (p * m + (p * m - k)) / (2 * p)) / 2)
        - (p * (((1 - p) * m + (m - x) + 2 * (p * m - k) / p) / (3 + (1 - p))) - (p * m - k)) *
          (((2 * (1 - p) * m + 2 * (m - x) + (p * m - k)) / (3 + (1 - p)) -
            ((1 - p) * m + (m - x) + 2 * (p * m - k) / p) / (3 + (1 - p))) / (2 * (1 - p)))
        = -NU / (8 * (4 - p) ^ 2 * (1 - p)) := by
      rw [hNU]; field_simp; ring
    have a1 : 0 < k - 2 * p * x := by linarith
    have a2 : 0 ≤ (2 - p) * x - k := by linarith
    have t1 : 0 ≤ (2 - p) * ((k - 2 * p * x) * ((2 - p) * x - k)) := by
      have : 0 < 2 - p := by linarith
      positivity
    have t2 : 0 ≤ (28 - 34 * p + 8 * p ^ 2) * (k * ((2 - p) * x - k)) := by
      have : 0 < 28 - 34 * p + 8 * p ^ 2 := by nlinarith
      positivity
    have t3 : 0 < p * (4 - p) ^ 2 * (1 - p) * k ^ 2 := by
      have : 0 < 4 - p := by linarith
      positivity
    have iden : (2 - p) ^ 2 * NU = -2 * ((2 - p) * ((k - 2 * p * x) * ((2 - p) * x - k)))
        - (28 - 34 * p + 8 * p ^ 2) * (k * ((2 - p) * x - k)) - p * (4 - p) ^ 2 * (1 - p) * k ^ 2 := by
      rw [hNU]; ring
    have hN : NU < 0 := by
      have h22 : 0 < (2 - p) ^ 2 := by have : 0 < 2 - p := by linarith
                                       positivity
      by_contra hc; push_neg at hc
      have := mul_nonneg h22.le hc
      linarith
    have : 0 < -NU / (8 * (4 - p) ^ 2 * (1 - p)) := by
      have : 0 < 4 - p := by linarith
      apply div_pos (by linarith); positivity
    linarith
  · have e : (1 - p) * ((m + (m - x)) / 2 - (m - x)) * ((m - (m + (m - x)) / 2) / 2)
        - ((2 * (1 - p) * m + 2 * (m - x) + (p * m - k)) / (3 + (1 - p)) - (m - x)) *
          (((1 - p) * m - (2 * (1 - p) * m + 2 * (m - x) + (p * m - k)) / (3 + (1 - p)) +
            p * (((1 - p) * m + (m - x) + 2 * (p * m - k) / p) / (3 + (1 - p)))) / (2 * (1 - p)))
        = (2 * k - p * (3 - p) * x) * ((p ^ 2 - 7 * p + 8) * x - 2 * k) / (8 * (4 - p) ^ 2 * (1 - p)) := by
      field_simp; ring
    have := R_ii p k x hp0 hp1 hx' h2' h3'
    linarith
  · set NB := (p ^ 4 - 10 * p ^ 3 + 33 * p ^ 2 - 28 * p) * x ^ 2 + 8 * p * k * x
        + (-p ^ 2 + 9 * p - 12) * k ^ 2 with hNB
    have e : (1 - p) * (m - ((2 * (1 - p) * m + 2 * (m - x) + (p * m - k)) / (3 + (1 - p)) -
          p * (((1 - p) * m + (m - x) + 2 * (p * m - k) / p) / (3 + (1 - p)))) / (1 - p)) ^ 2 / 4
        + p * (m - ((1 - p) * m + (m - x) + 2 * (p * m - k) / p) / (3 + (1 - p))) ^ 2 / 4
        - ((1 - p) * (m - (m + (m - x)) / 2) ^ 2 / 4 + p * (m - (p * m + (p * m - k)) / (2 * p)) ^ 2 / 4)
        = -NB / (16 * (4 - p) ^ 2 * (1 - p)) := by
      rw [hNB]; field_simp; ring
    set a := p * (p ^ 3 - 10 * p ^ 2 + 33 * p - 28) with ha
    have haneg : a < 0 := by
      have : p ^ 3 - 10 * p ^ 2 + 33 * p - 28 < 0 := by nlinarith
      rw [ha]; nlinarith
    have iden : 4 * a * NB = (2 * a * x + 8 * p * k) ^ 2
        + 4 * p * (7 - p) * (4 - p) ^ 2 * (3 - p) * (1 - p) * k ^ 2 := by
      rw [ha, hNB]; ring
    have t : 0 < 4 * p * (7 - p) * (4 - p) ^ 2 * (3 - p) * (1 - p) * k ^ 2 := by
      have : 0 < 7 - p := by linarith
      have : 0 < 4 - p := by linarith
      have : 0 < 3 - p := by linarith
      positivity
    have hN : NB < 0 := by
      by_contra hc; push_neg at hc
      have := mul_nonpos_of_nonpos_of_nonneg (by linarith : 4 * a ≤ 0) hc
      nlinarith [sq_nonneg (2 * a * x + 8 * p * k)]
    have : 0 < -NB / (16 * (4 - p) ^ 2 * (1 - p)) := by
      have : 0 < 4 - p := by linarith
      apply div_pos (by linarith); positivity
    linarith


/-- ρ=1 case (i-b) vs ρ=0 case (ii). -/
lemma cmp_ib_ii (m p cU cR wU0 wR0 U0 U1 R0 R1 B0 B1 : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hx : 0 < m - cR) (hk : 0 < p * m - cU)
    (h1 : p * m - cU ≤ 2 * p * (m - cR)) (h2 : p * m - cU ≤ (2 - p) * (m - cR))
    (h3 : p * (3 - p) * (m - cR) < 2 * (p * m - cU))
    (hwU0 : wU0 = ((1 - p) * m + cR + 2 * cU / p) / (3 + (1 - p)))
    (hwR0 : wR0 = (2 * (1 - p) * m + 2 * cR + cU) / (3 + (1 - p)))
    (hU0 : U0 = (p * wU0 - cU) * ((wR0 - wU0) / (2 * (1 - p))))
    (hU1 : U1 = (p * cR - cU) * ((m - cR) / 2))
    (hR0 : R0 = (wR0 - cR) * (((1 - p) * m - wR0 + p * wU0) / (2 * (1 - p))))
    (hR1 : R1 = (1 - p) * ((m + cR) / 2 - cR) * ((m - (m + cR) / 2) / 2))
    (hB0 : B0 = (1 - p) * (m - (wR0 - p * wU0) / (1 - p)) ^ 2 / 4 + p * (m - wU0) ^ 2 / 4)
    (hB1 : B1 = (1 - p) * (m - (m + cR) / 2) ^ 2 / 4 + p * (m - cR) ^ 2 / 4) :
    U0 < U1 ∧ R0 < R1 ∧ B1 < B0 := by
  have hp : p ≠ 0 := hp0.ne'
  have hq : 1 - p ≠ 0 := by intro h; linarith
  have hq0 : 0 < 1 - p := by linarith
  have h4 : (3 + (1 - p)) ≠ 0 := by intro h; linarith
  have h4' : (4 - p) ≠ 0 := by intro h; linarith
  have h4p : 0 < 4 - p := by linarith
  subst hwU0 hwR0 hU0 hU1 hR0 hR1 hB0 hB1
  obtain ⟨k, rfl⟩ : ∃ k, cU = p * m - k := ⟨p * m - cU, by ring⟩
  obtain ⟨x, rfl⟩ : ∃ x, cR = m - x := ⟨m - cR, by ring⟩
  have hx' : 0 < x := by linarith
  have hk' : 0 < k := by linarith
  have h1' : k ≤ 2 * p * x := by linarith
  have h2' : k ≤ (2 - p) * x := by linarith
  have h3' : p * (3 - p) * x < 2 * k := by linarith
  clear hx hk h1 h2 h3
  have a3 : 0 < 2 * k - p * (3 - p) * x := by linarith
  refine ⟨?_, ?_, ?_⟩
  · set Np := p ^ 5 * x ^ 2 - p ^ 4 * k * x - 9 * p ^ 4 * x ^ 2 + 9 * p ^ 3 * k * x + 24 * p ^ 3 * x ^ 2
        - p ^ 2 * k ^ 2 - 26 * p ^ 2 * k * x - 17 * p ^ 2 * x ^ 2 + 4 * p * k ^ 2 + 20 * p * k * x
        - 4 * k ^ 2 with hNp
    have e : (p * (m - x) - (p * m - k)) * ((m - (m - x)) / 2)
        - (p * (((1 - p) * m + (m - x) + 2 * (p * m - k) / p) / (3 + (1 - p))) - (p * m - k)) *
          (((2 * (1 - p) * m + 2 * (m - x) + (p * m - k)) / (3 + (1 - p)) -
            ((1 - p) * m + (m - x) + 2 * (p * m - k) / p) / (3 + (1 - p))) / (2 * (1 - p)))
        = Np / (2 * p * (4 - p) ^ 2 * (1 - p)) := by
      rw [hNp]; field_simp; ring
    have hc0 : 0 < 17 - 24 * p + 9 * p ^ 2 - p ^ 3 := by nlinarith
    have hN : 0 < Np := by
      rcases le_or_gt p (2 / 3) with hp23 | hp23
      · have b1 : 0 ≤ 2 * p * x - k := by linarith
        have hc2 : 0 < 7 - 12 * p + 5 * p ^ 2 - p ^ 3 := by nlinarith
        have iden : 2 * (3 - p) * (1 + p) * Np =
            (1 + p) * (17 - 24 * p + 9 * p ^ 2 - p ^ 3) * ((2 * p * x - k) * (2 * k - p * (3 - p) * x))
            + 2 * (4 - p) ^ 2 * (1 - p) ^ 2 * ((2 * p * x - k) * k)
            + (3 - p) * (7 - 12 * p + 5 * p ^ 2 - p ^ 3) * ((2 * k - p * (3 - p) * x) * k) := by
          rw [hNp]; ring
        have t1 : 0 ≤ (1 + p) * (17 - 24 * p + 9 * p ^ 2 - p ^ 3) *
            ((2 * p * x - k) * (2 * k - p * (3 - p) * x)) := by
          have : 0 < 1 + p := by linarith
          positivity
        have t2 : 0 ≤ 2 * (4 - p) ^ 2 * (1 - p) ^ 2 * ((2 * p * x - k) * k) := by positivity
        have t3 : 0 < (3 - p) * (7 - 12 * p + 5 * p ^ 2 - p ^ 3) * ((2 * k - p * (3 - p) * x) * k) := by
          have : 0 < 3 - p := by linarith
          positivity
        have hpos : 0 < 2 * (3 - p) * (1 + p) := by nlinarith
        by_contra hc; push_neg at hc
        have := mul_nonpos_of_nonneg_of_nonpos hpos.le hc
        linarith
      · have b2 : 0 ≤ (2 - p) * x - k := by linarith
        have iden : (3 - p) * (2 - p) * Np =
            p * (17 - 24 * p + 9 * p ^ 2 - p ^ 3) * (((2 - p) * x - k) * (2 * k - p * (3 - p) * x))
            + p * (4 - p) * (1 - p) * (2 - p) * (((2 - p) * x - k) * k)
            + (4 - p) * (1 - p) * (2 * p - 1) * (3 - p) * ((2 * k - p * (3 - p) * x) * k) := by
          rw [hNp]; ring
        have t1 : 0 ≤ p * (17 - 24 * p + 9 * p ^ 2 - p ^ 3) *
            (((2 - p) * x - k) * (2 * k - p * (3 - p) * x)) := by positivity
        have t2 : 0 ≤ p * (4 - p) * (1 - p) * (2 - p) * (((2 - p) * x - k) * k) := by
          have : 0 < 2 - p := by linarith
          positivity
        have t3 : 0 < (4 - p) * (1 - p) * (2 * p - 1) * (3 - p) * ((2 * k - p * (3 - p) * x) * k) := by
          have : 0 < 2 * p - 1 := by linarith
          have : 0 < 3 - p := by linarith
          positivity
        have hpos : 0 < (3 - p) * (2 - p) := by nlinarith
        by_contra hc; push_neg at hc
        have := mul_nonpos_of_nonneg_of_nonpos hpos.le hc
        linarith
    have : 0 < Np / (2 * p * (4 - p) ^ 2 * (1 - p)) := by positivity
    linarith
  · have e : (1 - p) * ((m + (m - x)) / 2 - (m - x)) * ((m - (m + (m - x)) / 2) / 2)
        - ((2 * (1 - p) * m + 2 * (m - x) + (p * m - k)) / (3 + (1 - p)) - (m - x)) *
          (((1 - p) * m - (2 * (1 - p) * m + 2 * (m - x) + (p * m - k)) / (3 + (1 - p)) +
            p * (((1 - p) * m + (m - x) + 2 * (p * m - k) / p) / (3 + (1 - p)))) / (2 * (1 - p)))
        = (2 * k - p * (3 - p) * x) * ((p ^ 2 - 7 * p + 8) * x - 2 * k) / (8 * (4 - p) ^ 2 * (1 - p)) := by
      field_simp; ring
    have := R_ii p k x hp0 hp1 hx' h2' h3'
    linarith
  · set G := 3 * p ^ 3 * x - 17 * p ^ 2 * x - 6 * p * k + 12 * p * x + 8 * k with hG
    have e : (1 - p) * (m - ((2 * (1 - p) * m + 2 * (m - x) + (p * m - k)) / (3 + (1 - p)) -
          p * (((1 - p) * m + (m - x) + 2 * (p * m - k) / p) / (3 + (1 - p)))) / (1 - p)) ^ 2 / 4
        + p * (m - ((1 - p) * m + (m - x) + 2 * (p * m - k) / p) / (3 + (1 - p))) ^ 2 / 4
        - ((1 - p) * (m - (m + (m - x)) / 2) ^ 2 / 4 + p * (m - (m - x)) ^ 2 / 4)
        = (2 * k - p * (3 - p) * x) * G / (16 * p * (4 - p) ^ 2 * (1 - p)) := by
      rw [hG]; field_simp; ring
    have hGp : 0 < G := by
      have iden : (3 - p) * G = 6 * p * (3 - p) * (1 - p) * (4 - p) * x
          + (3 - p) * (4 - 3 * p) * (2 * k - p * (3 - p) * x) := by rw [hG]; ring
      have : 0 < 3 - p := by linarith
      have : 0 < 4 - 3 * p := by linarith
      have t : 0 < 6 * p * (3 - p) * (1 - p) * (4 - p) * x
          + (3 - p) * (4 - 3 * p) * (2 * k - p * (3 - p) * x) := by positivity
      by_contra hc; push_neg at hc
      have := mul_nonpos_of_nonneg_of_nonpos (by linarith : (0:ℝ) ≤ 3 - p) hc
      linarith
    have : 0 < (2 * k - p * (3 - p) * x) * G / (16 * p * (4 - p) ^ 2 * (1 - p)) := by positivity
    linarith


/-! ### Thresholds in terms of k = P1 m - cU. -/

lemma psi1_eq (P : Params) (hP : P.Standing) :
    P.psi1 = P.m - (P.P1 * P.m - P.cU) / (2 * P.P1) := by
  have := hP.2.1.ne'; unfold Params.psi1; field_simp; ring

lemma phi1_eq (P : Params) : P.phi1 = P.m - (P.P1 * P.m - P.cU) / 2 := by
  unfold Params.phi1 Params.P0; ring

lemma phi2_eq (P : Params) (hP : P.Standing) :
    P.phi2 = P.m - (P.P1 * P.m - P.cU) / (2 - P.P1) := by
  have : (2 - P.P1) ≠ 0 := by have := hP.2.2.1; intro h; linarith
  unfold Params.phi2 Params.P0
  rw [show (1 - P.P1 + 1) = 2 - P.P1 by ring]; field_simp; ring

lemma psi2_eq (P : Params) (hP : P.Standing) :
    P.psi2 = P.m - 2 * (P.P1 * P.m - P.cU) / (P.P1 * (3 - P.P1)) := by
  have h0 := hP.2.1.ne'
  have : (3 - P.P1) ≠ 0 := by have := hP.2.2.1; intro h; linarith
  unfold Params.psi2 Params.P0
  rw [show (1 - P.P1 + 2) = 3 - P.P1 by ring]; field_simp; ring

lemma psi3_eq (P : Params) (hP : P.Standing) :
    P.psi3 = P.m - (2 - P.P1) * (P.P1 * P.m - P.cU) / P.P1 := by
  have h0 := hP.2.1.ne'
  unfold Params.psi3 Params.P0; field_simp; ring

lemma lt_aux (m a b c : ℝ) (hb : 0 < b) : m - a / b < c ↔ (m - c) * b < a := by
  rw [← lt_div_iff₀ hb]; constructor <;> intro h <;> linarith

lemma le_aux (m a b c : ℝ) (hb : 0 < b) : c ≤ m - a / b ↔ a ≤ (m - c) * b := by
  rw [← div_le_iff₀ hb]; constructor <;> intro h <;> linarith

lemma lt_aux' (m a b c : ℝ) (hb : 0 < b) : c < m - a / b ↔ a < (m - c) * b := by
  rw [← div_lt_iff₀ hb]; constructor <;> intro h <;> linarith

lemma psi3_le_psi2 (P : Params) (hP : P.Standing) : P.psi3 ≤ P.psi2 := by
  rw [psi3_eq P hP, psi2_eq P hP]
  obtain ⟨hm, hp0, hp1, hc0, hcm, -, -⟩ := hP
  have h3 : (3 - P.P1) ≠ 0 := by intro h; linarith
  have e : (2 - P.P1) * (P.P1 * P.m - P.cU) / P.P1 - 2 * (P.P1 * P.m - P.cU) / (P.P1 * (3 - P.P1))
      = (P.P1 * P.m - P.cU) * ((1 - P.P1) * (4 - P.P1)) / (P.P1 * (3 - P.P1)) := by
    field_simp; ring
  have : 0 ≤ (P.P1 * P.m - P.cU) * ((1 - P.P1) * (4 - P.P1)) / (P.P1 * (3 - P.P1)) := by
    apply div_nonneg
    · apply mul_nonneg (by linarith); apply mul_nonneg <;> linarith
    · apply mul_nonneg <;> linarith
  linarith

/-! ### Equilibrium summaries. -/

lemma rho1_summary (P : Params) (hP : P.Standing) (h : P.psi2 < P.cR) (w : Prices)
    (hw : P.IsEquilibrium 1 w) :
    w.wU = (if P.psi1 < P.cR then P.psi1 else P.cR) ∧
    P.payU 1 w = (P.P1 * w.wU - P.cU) * ((P.m - w.wU) / 2) ∧
    P.payR 1 w = (1 - P.P1) * ((P.m + P.cR) / 2 - P.cR) * ((P.m - (P.m + P.cR) / 2) / 2) ∧
    P.buyerValue 1 w = (1 - P.P1) * (P.m - (P.m + P.cR) / 2) ^ 2 / 4 + P.P1 * (P.m - w.wU) ^ 2 / 4 := by
  obtain ⟨hC, hU, hE, -, -⟩ := (proposition_2_i_corrected_v2 P hP h).2 w hw
  have hU' : w.wU = (if P.psi1 < P.cR then P.psi1 else P.cR) := by
    rw [hU]; unfold Params.priceI; split_ifs <;> rfl
  obtain ⟨hpU, hpR⟩ := pay1 P w hC
  obtain ⟨⟨hUf1, hUf2⟩, ⟨hRf1, hRf2, hRf3⟩, -, -⟩ := hw.1
  obtain ⟨hm, hp0, hp1, hc0, hcm, hr0, hrm⟩ := hP
  refine ⟨hU', hpU, by rw [hpR, hE], ?_⟩
  have hwU0 : 0 ≤ w.wU := le_trans (div_nonneg hc0 hp0.le) hUf1
  have hC1 := hC.1; have hC2 := hC.2
  rw [eta1_one] at hC2
  rw [bv1 P ⟨hm, hp0, hp1, hc0, hcm, hr0, hrm⟩ w hwU0 hUf2 hRf3 (by push_neg at hC1; linarith) hC2, hE]


lemma rho0_i_summary (P : Params) (hP : P.Standing) (h : P.psi3 < P.cR) (h2 : P.phi2 ≤ P.cR)
    (w : Prices) (hw : P.IsEquilibrium 0 w) :
    w.wU = P.priceN.wU ∧
    P.payU 0 w = (P.P1 * w.wU - P.cU) * ((P.m - w.wU) / 2) ∧
    P.payR 0 w = 0 ∧
    P.buyerValue 0 w = P.P1 * (P.m - w.wU) ^ 2 / 4 := by
  obtain ⟨hU, hi, -⟩ := (proposition_3_i_ii_corrected P hP h).2 w hw
  obtain ⟨hQR, hQU⟩ := hi h2
  obtain ⟨hQU', hUR, hR⟩ := order0_i P hP w hQR hQU
  obtain ⟨⟨hUf1, hUf2⟩, ⟨hRf1, hRf2, hRf3⟩, -, -⟩ := hw.1
  obtain ⟨hm, hp0, hp1, hc0, hcm, hr0, hrm⟩ := hP
  have hwU0 : 0 ≤ w.wU := le_trans (div_nonneg hc0 hp0.le) hUf1
  refine ⟨hU, ?_, ?_, ?_⟩
  · unfold Params.payU; rw [hQU']
  · unfold Params.payR; rw [hQR, PB0]; ring
  · exact bv0b P ⟨hm, hp0, hp1, hc0, hcm, hr0, hrm⟩ w hwU0 hUR.le hRf2 hUf2 hR

lemma rho0_ii_summary (P : Params) (hP : P.Standing) (h : P.psi3 < P.cR) (h2 : P.cR < P.phi2)
    (w : Prices) (hw : P.IsEquilibrium 0 w) :
    w.wU = P.priceN.wU ∧ w.wR = P.priceN.wR ∧
    P.payU 0 w = (P.P1 * w.wU - P.cU) * ((w.wR - w.wU) / (2 * (1 - P.P1))) ∧
    P.payR 0 w = (w.wR - P.cR) * (((1 - P.P1) * P.m - w.wR + P.P1 * w.wU) / (2 * (1 - P.P1))) ∧
    P.buyerValue 0 w = (1 - P.P1) * (P.m - (w.wR - P.P1 * w.wU) / (1 - P.P1)) ^ 2 / 4
        + P.P1 * (P.m - w.wU) ^ 2 / 4 := by
  obtain ⟨hU, -, hii⟩ := (proposition_3_i_ii_corrected P hP h).2 w hw
  obtain ⟨hR, hQU, hQR⟩ := hii h2
  obtain ⟨eU, eR, hUR, hR2⟩ := order0_ii P hP w hQR hQU
  obtain ⟨⟨hUf1, hUf2⟩, ⟨hRf1, hRf2, hRf3⟩, -, -⟩ := hw.1
  obtain ⟨hm, hp0, hp1, hc0, hcm, hr0, hrm⟩ := hP
  have hwU0 : 0 ≤ w.wU := le_trans (div_nonneg hc0 hp0.le) hUf1
  refine ⟨hU, hR, ?_, ?_, ?_⟩
  · unfold Params.payU; rw [eU]
  · unfold Params.payR; rw [eR, PB0]; ring
  · exact bv0a P ⟨hm, hp0, hp1, hc0, hcm, hr0, hrm⟩ w hwU0 hUR.le hRf2 hR2.le

lemma priceN_wU_ia (P : Params) (h : P.phi1 < P.cR) : P.priceN.wU = P.psi1 := by
  unfold Params.priceN; rw [if_pos h]

lemma priceN_wU_ib (P : Params) (h1 : P.cR ≤ P.phi1) (h2 : P.phi2 < P.cR) :
    P.priceN.wU = (P.cR - (1 - P.P1) * P.m) / P.P1 := by
  unfold Params.priceN; rw [if_neg (not_lt.mpr h1), if_pos h2, P0G0, P1G0]

lemma priceN_wU_b (P : Params) (hP : P.Standing) (h1 : P.cR ≤ P.phi1) (h2 : P.phi2 ≤ P.cR) :
    P.priceN.wU = (P.cR - (1 - P.P1) * P.m) / P.P1 := by
  rcases h2.lt_or_eq with h | h
  · exact priceN_wU_ib P h1 h
  · unfold Params.priceN; rw [if_neg (not_lt.mpr h1), if_neg (not_lt.mpr h.ge)]
    have hp0 := hP.2.1; have hp1 := hP.2.2.1
    have hpne : P.P1 ≠ 0 := hp0.ne'
    have h4 : (3 + P.P0) ≠ 0 := by unfold Params.P0; intro hh; linarith
    have h5 : (P.P0 + 1) ≠ 0 := by unfold Params.P0; intro hh; linarith
    have hc : P.cR = (2 * P.P0 * P.m + P.cU) / (P.P0 + 1) := by rw [← h]; rfl
    simp only
    rw [hc]
    unfold Params.P0 at h4 h5 ⊢
    field_simp
    ring

lemma priceN_ii (P : Params) (h1 : P.cR ≤ P.phi1) (h2 : P.cR ≤ P.phi2) :
    P.priceN.wU = ((1 - P.P1) * P.m + P.cR + 2 * P.cU / P.P1) / (3 + (1 - P.P1)) ∧
    P.priceN.wR = (2 * (1 - P.P1) * P.m + 2 * P.cR + P.cU) / (3 + (1 - P.P1)) := by
  unfold Params.priceN; rw [if_neg (not_lt.mpr h1), if_neg (not_lt.mpr h2)]
  simp [Params.P0]

end CSProp4Aux

namespace CSProp4Aux

lemma le_aux2 (m a b c : ℝ) (hb : 0 < b) : m - a / b ≤ c ↔ (m - c) * b ≤ a := by
  rw [← le_div_iff₀ hb]; constructor <;> intro h <;> linarith

end CSProp4Aux

open CSProp4Aux in
theorem solution (P : Params) (hP : P.Standing) :
    (P.psi2 < P.cR → (∃ w, P.IsEquilibrium 1 w) ∧ (∃ w, P.IsEquilibrium 0 w)) ∧
    ∀ wI wN : Prices, P.IsEquilibrium 1 wI → P.IsEquilibrium 0 wN →
      (P.phi1 ≤ P.cR →
        P.payU 1 wI = P.payU 0 wN ∧ P.buyerValue 0 wN ≤ P.buyerValue 1 wI ∧
        P.payR 0 wN ≤ P.payR 1 wI ∧
        (P.cR < P.m → P.buyerValue 0 wN < P.buyerValue 1 wI ∧ P.payR 0 wN < P.payR 1 wI)) ∧
      (P.buyerThreshold < P.cR → P.cR < P.phi1 →
        P.buyerValue 0 wN < P.buyerValue 1 wI ∧ P.payU 0 wN < P.payU 1 wI ∧
        P.payR 0 wN < P.payR 1 wI) ∧
      (P.psi2 < P.cR → P.cR ≤ P.buyerThreshold →
        P.buyerValue 1 wI ≤ P.buyerValue 0 wN ∧
        (P.cR < P.buyerThreshold → P.buyerValue 1 wI < P.buyerValue 0 wN) ∧
        P.payU 0 wN < P.payU 1 wI ∧ P.payR 0 wN < P.payR 1 wI) := by
  have hP' := hP
  obtain ⟨hm, hp0, hp1, hc0, hcm, hr0, hrm⟩ := hP'
  have hpsi32 := psi3_le_psi2 P hP
  refine ⟨fun h => ⟨⟨_, (proposition_2_i_corrected_v2 P hP h).1⟩,
    ⟨_, (proposition_3_i_ii_corrected P hP (lt_of_le_of_lt hpsi32 h)).1⟩⟩, ?_⟩
  intro wI wN hI hN
  -- notation
  obtain ⟨s, hsdef⟩ : ∃ s, s = Real.sqrt (4 - P.P1 + P.P1 ^ 2) := ⟨_, rfl⟩
  have hs2 : s ^ 2 = 4 - P.P1 + P.P1 ^ 2 := by rw [hsdef]; exact Real.sq_sqrt (by nlinarith)
  have hs0 : 0 ≤ s := by rw [hsdef]; exact Real.sqrt_nonneg _
  have hs2p : 2 * P.P1 < s := by nlinarith
  have hs2m : 2 - P.P1 < s := by nlinarith
  have hs3 : P.P1 * (3 - P.P1) < 2 * s := by nlinarith
  have hs4 : s < 2 := by nlinarith
  have hq3 : 0 < 4 - P.P1 * (3 - P.P1) := by nlinarith
  have hq3' : 0 ≤ P.P1 * (3 - P.P1) := by nlinarith
  have ht : P.buyerThreshold = P.m - (P.P1 * P.m - P.cU) / s := by rw [hsdef]; rfl
  have hk0 : 0 ≤ P.P1 * P.m - P.cU := by linarith
  have hspos : 0 < s := by linarith
  have c_psi2 : P.psi2 < P.cR ↔ (P.m - P.cR) * (P.P1 * (3 - P.P1)) < 2 * (P.P1 * P.m - P.cU) := by
    rw [psi2_eq P hP]; exact lt_aux _ _ _ _ (by nlinarith)
  have c_psi1 : P.psi1 < P.cR ↔ (P.m - P.cR) * (2 * P.P1) < P.P1 * P.m - P.cU := by
    rw [psi1_eq P hP]; exact lt_aux _ _ _ _ (by linarith)
  have c_phi1 : P.phi1 ≤ P.cR ↔ (P.m - P.cR) * 2 ≤ P.P1 * P.m - P.cU := by
    rw [phi1_eq P]; exact le_aux2 _ _ _ _ (by norm_num)
  have c_phi1' : P.cR < P.phi1 ↔ P.P1 * P.m - P.cU < (P.m - P.cR) * 2 := by
    rw [phi1_eq P]; exact lt_aux' _ _ _ _ (by norm_num)
  have c_phi2 : P.phi2 < P.cR ↔ (P.m - P.cR) * (2 - P.P1) < P.P1 * P.m - P.cU := by
    rw [phi2_eq P hP]; exact lt_aux _ _ _ _ (by linarith)
  have c_t : P.buyerThreshold < P.cR ↔ (P.m - P.cR) * s < P.P1 * P.m - P.cU := by
    rw [ht]; exact lt_aux _ _ _ _ hspos
  have c_t' : P.cR ≤ P.buyerThreshold ↔ P.P1 * P.m - P.cU ≤ (P.m - P.cR) * s := by
    rw [ht]; exact le_aux _ _ _ _ hspos
  have c_t'' : P.cR < P.buyerThreshold ↔ P.P1 * P.m - P.cU < (P.m - P.cR) * s := by
    rw [ht]; exact lt_aux' _ _ _ _ hspos
  refine ⟨?_, ?_, ?_⟩
  · -- part (i)
    intro hphi
    rcases hk0.lt_or_eq with hk | hk
    · have hx0 : 0 ≤ P.m - P.cR := by linarith
      have hphi' := c_phi1.mp hphi
      have hpsi2 : P.psi2 < P.cR := c_psi2.mpr (by have h1 := mul_pos hk hq3; have h2 := mul_nonneg hq3' (show (0:ℝ) ≤ (P.P1 * P.m - P.cU) - 2 * (P.m - P.cR) by linarith); linarith)
      have hpsi1 : P.psi1 < P.cR := c_psi1.mpr (by have h1 := mul_le_mul_of_nonneg_left hphi' hp0.le; have h2 := mul_lt_mul_of_pos_right hp1 hk; linarith)
      have hphi2 : P.phi2 < P.cR := c_phi2.mpr (by have h1 := mul_nonneg (show (0:ℝ) ≤ 1 - P.P1 / 2 by linarith) (show (0:ℝ) ≤ (P.P1 * P.m - P.cU) - 2 * (P.m - P.cR) by linarith); have h2 := mul_pos hp0 hk; linarith)
      obtain ⟨hU1, pU1, pR1, b1⟩ := rho1_summary P hP hpsi2 wI hI
      rw [if_pos hpsi1] at hU1
      obtain ⟨hU0, pU0, pR0, b0⟩ := rho0_i_summary P hP (lt_of_le_of_lt hpsi32 hpsi2) hphi2.le wN hN
      have hU0' : wN.wU = P.psi1 := by
        rw [hU0]
        rcases hphi.lt_or_eq with h | h
        · exact priceN_wU_ia P h
        · rw [priceN_wU_ib P h.ge hphi2, ← h, phi1_eq P, psi1_eq P hP]
          field_simp; ring
      rw [pU1, pU0, pR1, pR0, b1, b0, hU1, hU0']
      refine ⟨rfl, ?_, ?_, ?_⟩
      · have := mul_nonneg (show (0:ℝ) ≤ 1 - P.P1 by linarith) (sq_nonneg (P.m - (P.m + P.cR) / 2)); linarith
      · have : 0 ≤ (P.m + P.cR) / 2 - P.cR := by linarith
        have : 0 ≤ (P.m - (P.m + P.cR) / 2) / 2 := by linarith
        have : (0:ℝ) ≤ 1 - P.P1 := by linarith
        positivity
      · intro hlt
        have : 0 < (P.m + P.cR) / 2 - P.cR := by linarith
        have : 0 < (P.m - (P.m + P.cR) / 2) / 2 := by linarith
        have : (0:ℝ) < 1 - P.P1 := by linarith
        have : 0 < P.m - (P.m + P.cR) / 2 := by linarith
        constructor
        · have : 0 < (1 - P.P1) * (P.m - (P.m + P.cR) / 2) ^ 2 / 4 := by positivity
          linarith
        · positivity
    · -- degenerate case cU = P1 m
      have hcU : P.cU = P.P1 * P.m := by linarith
      have hcR : P.cR = P.m := by
        have := c_phi1.mp hphi; rw [← hk] at this; linarith
      have hcUp : P.cU / P.P1 = P.m := by rw [hcU]; field_simp
      obtain ⟨⟨hIU1, hIU2⟩, ⟨hIR1, hIR2, hIR3⟩, -, -⟩ := hI.1
      obtain ⟨⟨hNU1, hNU2⟩, ⟨hNR1, hNR2, hNR3⟩, -, -⟩ := hN.1
      have eIU : wI.wU = P.m := by linarith
      have eNU : wN.wU = P.m := by linarith
      have eIR : wI.wR = P.m := by linarith
      have eIE : wI.wE = P.m := by linarith
      have eNR : wN.wR = P.m := by linarith
      have eNE : wN.wE = P.m := by linarith
      have b1 := bv1 P hP wI (by linarith) (by linarith) hIR3 (by linarith) (by rw [eIU, eIE, eIR]; linarith)
      have b0 := bv0b P hP wN (by linarith) (by linarith) hNR2 hNU2 (by rw [eNU, eNR]; linarith)
      have zU1 : P.payU 1 wI = 0 := by
        have : P.P1 * wI.wU - P.cU = 0 := by rw [eIU]; linarith
        unfold Params.payU; rw [this, zero_mul]
      have zU0 : P.payU 0 wN = 0 := by
        have : P.P1 * wN.wU - P.cU = 0 := by rw [eNU]; linarith
        unfold Params.payU; rw [this, zero_mul]
      have zR1 : P.payR 1 wI = 0 := by
        unfold Params.payR; rw [eIR, eIE, hcR]; simp
      have zR0 : P.payR 0 wN = 0 := by
        unfold Params.payR; rw [eNR, eNE, hcR]; simp
      have zB1 : P.buyerValue 1 wI = 0 := by rw [b1, eIU, eIE]; ring
      have zB0 : P.buyerValue 0 wN = 0 := by rw [b0, eNU]; ring
      rw [zU1, zU0, zR1, zR0, zB1, zB0]
      exact ⟨rfl, le_rfl, le_rfl, fun h => absurd h (by rw [hcR]; exact lt_irrefl _)⟩
  · -- part (ii)
    intro htc hphi
    have ht' := c_t.mp htc
    have hphi' := c_phi1'.mp hphi
    have hx : 0 < P.m - P.cR := by
      by_contra hc; push_neg at hc
      have := mul_nonneg_of_nonpos_of_nonpos hc (show s - 2 ≤ 0 by linarith); linarith
    have hk : 0 < P.P1 * P.m - P.cU := by have := mul_pos hx hspos; linarith
    have hpsi2 : P.psi2 < P.cR := c_psi2.mpr (by have := mul_lt_mul_of_pos_left hs3 hx; linarith)
    have hpsi1 : P.psi1 < P.cR := c_psi1.mpr (by have := mul_lt_mul_of_pos_left hs2p hx; linarith)
    have hphi2 : P.phi2 < P.cR := c_phi2.mpr (by have := mul_lt_mul_of_pos_left hs2m hx; linarith)
    obtain ⟨hU1, pU1, pR1, b1⟩ := rho1_summary P hP hpsi2 wI hI
    rw [if_pos hpsi1] at hU1
    obtain ⟨hU0, pU0, pR0, b0⟩ := rho0_i_summary P hP (lt_of_le_of_lt hpsi32 hpsi2) hphi2.le wN hN
    rw [priceN_wU_ib P hphi.le hphi2] at hU0
    obtain ⟨-, eU, eB, hR⟩ := cmp_ia_ib P.m P.P1 P.cU P.cR wI.wU wN.wU hp0 hp1 hx (by rw [hU1]; rfl) hU0
    rw [pU1, pU0, pR1, pR0, b1, b0]
    refine ⟨?_, ?_, hR⟩
    · have : 0 < ((P.P1 * P.m - P.cU) ^ 2 - (4 - P.P1 + P.P1 ^ 2) * (P.m - P.cR) ^ 2) / (16 * P.P1) := by
        apply div_pos _ (by linarith)
        rw [← hs2]
        have : 0 ≤ (P.m - P.cR) * s := by positivity
        have := mul_self_lt_mul_self this ht'; linarith
      linarith
    · have : 0 < ((P.P1 * P.m - P.cU) - 2 * (P.m - P.cR)) ^ 2 / (8 * P.P1) := by
        apply div_pos _ (by linarith)
        have : (P.P1 * P.m - P.cU) - 2 * (P.m - P.cR) ≠ 0 := by intro h; linarith
        positivity
      linarith
  · -- part (iii)
    intro hpsi2 htc
    have hpsi2' := c_psi2.mp hpsi2
    have ht' := c_t'.mp htc
    have hk : 0 < P.P1 * P.m - P.cU := by
      rcases hk0.lt_or_eq with h | h
      · exact h
      · exfalso; rw [← h] at hpsi2'; have := mul_nonneg (show (0:ℝ) ≤ P.m - P.cR by linarith) hq3'; linarith
    have hx : 0 < P.m - P.cR := by
      by_contra hc; push_neg at hc
      have := mul_le_mul_of_nonneg_right hc hs0; linarith
    have hphi : P.cR < P.phi1 := c_phi1'.mpr (by have := mul_lt_mul_of_pos_left hs4 hx; linarith)
    have hpsi3 := lt_of_le_of_lt hpsi32 hpsi2
    obtain ⟨hU1, pU1, pR1, b1⟩ := rho1_summary P hP hpsi2 wI hI
    by_cases hpsi1 : P.psi1 < P.cR
    · rw [if_pos hpsi1] at hU1
      have hpsi1' := c_psi1.mp hpsi1
      by_cases hphi2 : P.phi2 ≤ P.cR
      · obtain ⟨hU0, pU0, pR0, b0⟩ := rho0_i_summary P hP hpsi3 hphi2 wN hN
        rw [priceN_wU_b P hP hphi.le hphi2] at hU0
        obtain ⟨-, eU, eB, hR⟩ := cmp_ia_ib P.m P.P1 P.cU P.cR wI.wU wN.wU hp0 hp1 hx (by rw [hU1]; rfl) hU0
        rw [pU1, pU0, pR1, pR0, b1, b0]
        have hsx : (P.P1 * P.m - P.cU) ^ 2 ≤ (4 - P.P1 + P.P1 ^ 2) * (P.m - P.cR) ^ 2 := by
          rw [← hs2]; have := mul_self_le_mul_self hk.le ht'; linarith
        refine ⟨?_, ?_, ?_, hR⟩
        · have : ((P.P1 * P.m - P.cU) ^ 2 - (4 - P.P1 + P.P1 ^ 2) * (P.m - P.cR) ^ 2) / (16 * P.P1) ≤ 0 :=
            div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
          linarith
        · intro hlt
          have hlt' := c_t''.mp hlt
          have : ((P.P1 * P.m - P.cU) ^ 2 - (4 - P.P1 + P.P1 ^ 2) * (P.m - P.cR) ^ 2) / (16 * P.P1) < 0 := by
            apply div_neg_of_neg_of_pos _ (by linarith)
            rw [← hs2]; have := mul_self_lt_mul_self hk.le hlt'; linarith
          linarith
        · have : 0 < ((P.P1 * P.m - P.cU) - 2 * (P.m - P.cR)) ^ 2 / (8 * P.P1) := by
            apply div_pos _ (by linarith)
            have : (P.P1 * P.m - P.cU) - 2 * (P.m - P.cR) ≠ 0 := by
              intro h; have := c_phi1'.mp hphi; linarith
            positivity
          linarith
      · push_neg at hphi2
        have hphi2' : P.P1 * P.m - P.cU ≤ (P.m - P.cR) * (2 - P.P1) := by
          by_contra hc; push_neg at hc; exact absurd (c_phi2.mpr hc) (not_lt.mpr hphi2.le)
        obtain ⟨hU0, hR0, pU0, pR0, b0⟩ := rho0_ii_summary P hP hpsi3 hphi2 wN hN
        obtain ⟨eU0, eR0⟩ := priceN_ii P hphi.le hphi2.le
        rw [eU0] at hU0; rw [eR0] at hR0
        obtain ⟨h1, h2, h3⟩ := cmp_ia_ii P.m P.P1 P.cU P.cR wN.wU wN.wR (P.payU 0 wN) (P.payU 1 wI) (P.payR 0 wN) (P.payR 1 wI)
          (P.buyerValue 0 wN) (P.buyerValue 1 wI) hp0 hp1 hx hk
          (by linarith) (by linarith) (by linarith) hU0 hR0 pU0 (by rw [pU1, hU1]; rfl) pR0 pR1 b0
          (by rw [b1, hU1]; rfl)
        exact ⟨h3.le, fun _ => h3, h1, h2⟩
    · push_neg at hpsi1
      rw [if_neg (not_lt.mpr hpsi1)] at hU1
      have hpsi1' : P.P1 * P.m - P.cU ≤ (P.m - P.cR) * (2 * P.P1) := by
        by_contra hc; push_neg at hc; exact absurd (c_psi1.mpr hc) (not_lt.mpr hpsi1)
      by_cases hphi2 : P.phi2 ≤ P.cR
      · obtain ⟨hU0, pU0, pR0, b0⟩ := rho0_i_summary P hP hpsi3 hphi2 wN hN
        rw [priceN_wU_b P hP hphi.le hphi2] at hU0
        obtain ⟨hUlt, hBlt⟩ := cmp_ib_ib P.m P.P1 P.cU P.cR wN.wU hp0 hp1 hx hk (by linarith) hU0
        rw [pU1, pU0, pR1, pR0, b1, b0, hU1]
        have hR : 0 < (1 - P.P1) * ((P.m + P.cR) / 2 - P.cR) * ((P.m - (P.m + P.cR) / 2) / 2) := by
          have : 0 < (P.m + P.cR) / 2 - P.cR := by linarith
          have : 0 < (P.m - (P.m + P.cR) / 2) / 2 := by linarith
          have : (0:ℝ) < 1 - P.P1 := by linarith
          positivity
        exact ⟨hBlt.le, fun _ => hBlt, hUlt, hR⟩
      · push_neg at hphi2
        have hphi2' : P.P1 * P.m - P.cU ≤ (P.m - P.cR) * (2 - P.P1) := by
          by_contra hc; push_neg at hc; exact absurd (c_phi2.mpr hc) (not_lt.mpr hphi2.le)
        obtain ⟨hU0, hR0, pU0, pR0, b0⟩ := rho0_ii_summary P hP hpsi3 hphi2 wN hN
        obtain ⟨eU0, eR0⟩ := priceN_ii P hphi.le hphi2.le
        rw [eU0] at hU0; rw [eR0] at hR0
        obtain ⟨h1, h2, h3⟩ := cmp_ib_ii P.m P.P1 P.cU P.cR wN.wU wN.wR (P.payU 0 wN) (P.payU 1 wI) (P.payR 0 wN) (P.payR 1 wI)
          (P.buyerValue 0 wN) (P.buyerValue 1 wI) hp0 hp1 hx hk
          (by linarith) (by linarith) (by linarith) hU0 hR0 pU0 (by rw [pU1, hU1]) pR0 pR1 b0
          (by rw [b1, hU1])
        exact ⟨h3.le, fun _ => h3, h1, h2⟩
