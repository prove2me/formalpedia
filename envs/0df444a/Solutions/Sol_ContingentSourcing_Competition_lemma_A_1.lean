-- Prove2me | solution 1 for ContingentSourcing.Competition.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T07:28:33.288689+00:00
-- url     : https://prove2.me/submissions/cf4b616b-7b66-4dd9-8b83-e33d27f83e77

import Mathlib
import Definitions.Def_ContingentSourcing_Competition_Model

open ContingentSourcing.Competition

namespace CSLA1

/-- Supplier R's payoff at ρ = 1 as a function of (w_U, w_R, w_E). -/
noncomputable def Rf (P : Params) (u r e : ℝ) : ℝ :=
  if r ≤ u then (r - P.cR) * ((P.m - r) / 2)
  else if P.P1 * u + (1 - P.P1) * e ≤ r then (1 - P.P1) * (e - P.cR) * ((P.m - e) / 2)
  else (r - P.cR) * (((1 - P.P1) * P.m - r + P.P1 * u) / (2 * (1 - P.P1)))

lemma eta1_one (P : Params) (w : Prices) : P.eta1 1 w = P.P1 * w.wU + (1 - P.P1) * w.wE := by
  simp [Params.eta1, Params.PB, Params.PG, Params.P0G, Params.P0]

lemma eta2_eq (P : Params) (w : Prices) : P.eta2 w = P.P1 * w.wU + (1 - P.P1) * w.wE := by
  simp [Params.eta2, Params.P0]

lemma payR_eq (P : Params) (w : Prices) : P.payR 1 w = Rf P w.wU w.wR w.wE := by
  unfold Params.payR Params.order Rf
  rw [eta1_one, eta2_eq]
  split_ifs with h1 h2 h3
  · simp [Params.orderIV]
  · simp [Params.orderI, Params.PB, Params.P0]; try ring
  · exfalso; push_neg at h2; linarith
  · simp [Params.orderIII, Params.P0]; try ring

lemma Rf_IV (P : Params) (u r e : ℝ) (h : r ≤ u) : Rf P u r e = (r - P.cR) * ((P.m - r) / 2) := by
  unfold Rf; rw [if_pos h]
lemma Rf_I (P : Params) (u r e : ℝ) (h1 : u < r) (h2 : P.P1 * u + (1 - P.P1) * e ≤ r) :
    Rf P u r e = (1 - P.P1) * (e - P.cR) * ((P.m - e) / 2) := by
  unfold Rf; rw [if_neg (not_le.mpr h1), if_pos h2]
lemma Rf_M (P : Params) (u r e : ℝ) (h1 : u < r) (h2 : r < P.P1 * u + (1 - P.P1) * e) :
    Rf P u r e = (r - P.cR) * (((1 - P.P1) * P.m - r + P.P1 * u) / (2 * (1 - P.P1))) := by
  unfold Rf; rw [if_neg (not_le.mpr h1), if_neg (not_le.mpr h2)]

lemma BR_of (P : Params) (u r e V : ℝ) (hf : P.RFeasible r e) (hv : Rf P u r e = V)
    (hb : ∀ r' e', P.RFeasible r' e' → Rf P u r' e' ≤ V) : P.IsBestResponseR 1 u r e := by
  refine ⟨hf, fun r' e' h' => ?_⟩
  rw [payR_eq, payR_eq]; simp only; rw [hv]; exact hb r' e' h'

lemma BR_val (P : Params) (u r e V r0 e0 : ℝ) (hBR : P.IsBestResponseR 1 u r e)
    (h0 : P.RFeasible r0 e0) (hv0 : Rf P u r0 e0 = V)
    (hb : ∀ r' e', P.RFeasible r' e' → Rf P u r' e' ≤ V) : Rf P u r e = V := by
  have h1 := hBR.2 r0 e0 h0
  rw [payR_eq, payR_eq] at h1; simp only at h1
  have h2 := hb r e hBR.1
  linarith

/-- Sole-sourcing region payoff versus its vertex. -/
lemma RIV_vertex (P : Params) (r : ℝ) :
    (r - P.cR) * ((P.m - r) / 2) = (P.m - P.cR) ^ 2 / 8 - (r - (P.m + P.cR) / 2) ^ 2 / 2 := by ring

/-- Contingent region payoff versus its vertex. -/
lemma RI_vertex (P : Params) (e : ℝ) :
    (1 - P.P1) * (e - P.cR) * ((P.m - e) / 2) =
      (1 - P.P1) * (P.m - P.cR) ^ 2 / 8 - (1 - P.P1) * (e - (P.m + P.cR) / 2) ^ 2 / 2 := by ring

/-- Diversification region payoff versus its vertex. -/
lemma RM_vertex (P : Params) (hq : 0 < 1 - P.P1) (u r : ℝ) :
    (r - P.cR) * (((1 - P.P1) * P.m - r + P.P1 * u) / (2 * (1 - P.P1))) =
      ((P.P1 * u + (1 - P.P1) * P.m - P.cR) ^ 2 / 4
        - (r - (P.P1 * u + (1 - P.P1) * P.m + P.cR) / 2) ^ 2) / (2 * (1 - P.P1)) := by
  field_simp; ring

/-- RM at u equals RIV at u. -/
lemma RM_at_u (P : Params) (hq : 0 < 1 - P.P1) (u : ℝ) :
    (u - P.cR) * (((1 - P.P1) * P.m - u + P.P1 * u) / (2 * (1 - P.P1))) =
      (u - P.cR) * ((P.m - u) / 2) := by
  field_simp; ring

/-- Diversification payoff dominates sole-sourcing payoff at prices r ∈ [c_R, u]. -/
lemma RIV_le_RM (P : Params) (hP : P.Standing) (u r : ℝ) (h1 : P.cR ≤ r) (h2 : r ≤ u) :
    (r - P.cR) * ((P.m - r) / 2) ≤
      (r - P.cR) * (((1 - P.P1) * P.m - r + P.P1 * u) / (2 * (1 - P.P1))) := by
  have hp0 := hP.2.1; have hq : 0 < 1 - P.P1 := by linarith [hP.2.2.1]
  have e : (r - P.cR) * (((1 - P.P1) * P.m - r + P.P1 * u) / (2 * (1 - P.P1))) -
      (r - P.cR) * ((P.m - r) / 2) = (r - P.cR) * (P.P1 * (u - r)) / (2 * (1 - P.P1)) := by
    field_simp; ring
  have : 0 ≤ (r - P.cR) * (P.P1 * (u - r)) / (2 * (1 - P.P1)) := by
    apply div_nonneg _ (by linarith)
    exact mul_nonneg (by linarith) (mul_nonneg hp0.le (by linarith))
  linarith

/-- The key strict inequality: undercutting at u beats the contingent maximum. -/
lemma undercut_beats (P : Params) (hP : P.Standing) (u : ℝ)
    (hE : (1 - P.P1) * P.m + P.cR < (2 - P.P1) * u) (he : 2 * u ≤ P.m + P.cR) :
    (1 - P.P1) * (P.m - P.cR) ^ 2 / 8 < (u - P.cR) * ((P.m - u) / 2) := by
  obtain ⟨hm, hp0, hp1, hc0, hcm, hr0, hrm⟩ := hP
  set t := u - P.cR with ht
  set z := P.m - P.cR with hz
  have hA : 0 < (2 - P.P1) * t - (1 - P.P1) * z := by rw [ht, hz]; linarith
  have ht0 : 0 < t := by
    by_contra hc; push_neg at hc
    have := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - P.P1) (by rw [hz]; linarith : (0:ℝ) ≤ z)
    have := mul_le_mul_of_nonneg_left hc (by linarith : (0:ℝ) ≤ 2 - P.P1)
    linarith
  have hz0 : 0 < z := by rw [hz]; rw [ht] at ht0; linarith
  have hB : 0 < z - (2 - P.P1) * t := by
    have : 2 * t ≤ z := by rw [ht, hz]; linarith
    have := mul_lt_mul_of_pos_right (by linarith : 1 - P.P1 < 1) ht0
    linarith
  have iden : (2 - P.P1) ^ 2 * (4 * t * (z - t) - (1 - P.P1) * z ^ 2) =
      4 * ((2 - P.P1) * t - (1 - P.P1) * z) * (z - (2 - P.P1) * t)
      + (1 - P.P1) * P.P1 * (4 - P.P1) * z ^ 2 := by ring
  have hpos : 0 < (2 - P.P1) ^ 2 * (4 * t * (z - t) - (1 - P.P1) * z ^ 2) := by
    rw [iden]
    have := mul_pos hA hB
    have : 0 ≤ (1 - P.P1) * P.P1 * (4 - P.P1) * z ^ 2 := by
      have : (0:ℝ) < 4 - P.P1 := by linarith
      have : (0:ℝ) < 1 - P.P1 := by linarith
      positivity
    linarith
  have h4 : 0 < 4 * t * (z - t) - (1 - P.P1) * z ^ 2 := by
    by_contra hh; push_neg at hh
    have := mul_nonpos_of_nonneg_of_nonpos (by positivity : (0:ℝ) ≤ (2 - P.P1) ^ 2) hh
    linarith
  have e3 : (u - P.cR) * ((P.m - u) / 2) = t * (z - t) / 2 := by rw [ht, hz]; ring
  rw [e3]
  linarith

/-- In the diversification region above u, R's payoff is below its sole-sourcing payoff at u
when the parabola's vertex is at most u. -/
lemma RM_lt_RIVu (P : Params) (hP : P.Standing) (u r : ℝ)
    (hrs : (1 - P.P1) * P.m + P.cR ≤ (2 - P.P1) * u) (hr : u < r) :
    (r - P.cR) * (((1 - P.P1) * P.m - r + P.P1 * u) / (2 * (1 - P.P1))) <
      (u - P.cR) * ((P.m - u) / 2) := by
  have hq : 0 < 1 - P.P1 := by linarith [hP.2.2.1]
  rw [← RM_at_u P hq u, RM_vertex P hq u r, RM_vertex P hq u u]
  apply div_lt_div_of_pos_right _ (by linarith)
  have h1 : (P.P1 * u + (1 - P.P1) * P.m + P.cR) / 2 ≤ u := by linarith
  nlinarith

lemma case_i (P : Params) (hP : P.Standing) (u : ℝ) (hu : (P.m + P.cR) / 2 < u) (hum : u ≤ P.m) :
    (∀ e, (P.m + P.cR) / 2 ≤ e → e ≤ P.m → P.IsBestResponseR 1 u ((P.m + P.cR) / 2) e) ∧
    (∀ r e, P.IsBestResponseR 1 u r e → r = (P.m + P.cR) / 2) := by
  have hP' := hP
  obtain ⟨hm, hp0, hp1, hc0, hcm, hr0, hrm⟩ := hP'
  have hq : 0 < 1 - P.P1 := by linarith
  have hcm' : P.cR < P.m := by linarith
  have hrs : (1 - P.P1) * P.m + P.cR ≤ (2 - P.P1) * u := by
    have := mul_le_mul_of_nonneg_left hu.le (by linarith : (0:ℝ) ≤ 2 - P.P1)
    nlinarith
  have bound : ∀ r e, P.RFeasible r e → Rf P u r e ≤ (P.m - P.cR) ^ 2 / 8 := by
    intro r e ⟨g1, g2, g3⟩
    unfold Rf
    split_ifs with k1 k2
    · rw [RIV_vertex]; nlinarith [sq_nonneg (r - (P.m + P.cR) / 2)]
    · rw [RI_vertex]
      have := mul_nonneg hq.le (sq_nonneg (e - (P.m + P.cR) / 2))
      have := mul_le_mul_of_nonneg_right (by linarith : 1 - P.P1 ≤ 1) (sq_nonneg (P.m - P.cR))
      linarith
    · push_neg at k1
      have := RM_lt_RIVu P hP u r hrs k1
      rw [RIV_vertex] at this
      nlinarith [sq_nonneg (u - (P.m + P.cR) / 2)]
  have attain : ∀ e, Rf P u ((P.m + P.cR) / 2) e = (P.m - P.cR) ^ 2 / 8 := by
    intro e; rw [Rf_IV P _ _ _ hu.le, RIV_vertex]; ring
  refine ⟨fun e he1 he2 => BR_of P u _ e _ ⟨by linarith, he1, he2⟩ (attain e) bound, ?_⟩
  intro r e hBR
  have hv := BR_val P u r e _ _ P.m hBR ⟨by linarith, by linarith, le_rfl⟩ (attain P.m) bound
  obtain ⟨g1, g2, g3⟩ := hBR.1
  unfold Rf at hv
  split_ifs at hv with k1 k2
  · rw [RIV_vertex] at hv
    have : (r - (P.m + P.cR) / 2) ^ 2 = 0 := by linarith
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    linarith
  · exfalso
    rw [RI_vertex] at hv
    have := mul_nonneg hq.le (sq_nonneg (e - (P.m + P.cR) / 2))
    have : 0 < P.P1 * (P.m - P.cR) ^ 2 := by
      have : P.m - P.cR ≠ 0 := by linarith
      positivity
    nlinarith
  · exfalso
    push_neg at k1
    have := RM_lt_RIVu P hP u r hrs k1
    rw [RIV_vertex] at this
    have : 0 < (u - (P.m + P.cR) / 2) ^ 2 := by
      have : u - (P.m + P.cR) / 2 ≠ 0 := by linarith
      positivity
    linarith

lemma case_ii (P : Params) (hP : P.Standing) (u : ℝ)
    (hE : (1 - P.P1) * P.m + P.cR < (2 - P.P1) * u) (hu : u ≤ (P.m + P.cR) / 2) :
    (∀ e, u ≤ e → e ≤ P.m → P.IsBestResponseR 1 u u e) ∧
    (∀ r e, P.IsBestResponseR 1 u r e → r = u) := by
  have hP' := hP
  obtain ⟨hm, hp0, hp1, hc0, hcm, hr0, hrm⟩ := hP'
  have hq : 0 < 1 - P.P1 := by linarith
  have hcu : P.cR < u := by
    by_contra hc; push_neg at hc
    have := mul_le_mul_of_nonneg_left hc (by linarith : (0:ℝ) ≤ 2 - P.P1)
    have := mul_le_mul_of_nonneg_left hrm hq.le
    linarith
  have hund := undercut_beats P hP u hE (by linarith)
  set V := (u - P.cR) * ((P.m - u) / 2) with hV
  have bound : ∀ r e, P.RFeasible r e → Rf P u r e ≤ V := by
    intro r e ⟨g1, g2, g3⟩
    unfold Rf
    split_ifs with k1 k2
    · rw [hV]
      have : 0 ≤ (u - r) * (P.m + P.cR - u - r) := mul_nonneg (by linarith) (by linarith)
      nlinarith
    · rw [RI_vertex]
      have := mul_nonneg hq.le (sq_nonneg (e - (P.m + P.cR) / 2))
      linarith
    · push_neg at k1
      exact (RM_lt_RIVu P hP u r hE.le k1).le
  have attain : ∀ e, Rf P u u e = V := by intro e; rw [Rf_IV P _ _ _ le_rfl]
  refine ⟨fun e he1 he2 => BR_of P u u e V ⟨hcu.le, he1, he2⟩ (attain e) bound, ?_⟩
  intro r e hBR
  have hv := BR_val P u r e V u P.m hBR ⟨hcu.le, by linarith, le_rfl⟩ (attain P.m) bound
  obtain ⟨g1, g2, g3⟩ := hBR.1
  unfold Rf at hv
  split_ifs at hv with k1 k2
  · rw [hV] at hv
    have e0 : (u - r) * (P.m + P.cR - u - r) = 0 := by linarith
    rcases mul_eq_zero.mp e0 with h0 | h0
    · linarith
    · linarith
  · exfalso
    rw [RI_vertex] at hv
    have := mul_nonneg hq.le (sq_nonneg (e - (P.m + P.cR) / 2))
    linarith
  · exfalso
    push_neg at k1
    have := RM_lt_RIVu P hP u r hE.le k1
    linarith

lemma case_iii (P : Params) (hP : P.Standing) (u : ℝ) (hcu : P.cR < u)
    (hE : (2 - P.P1) * u ≤ (1 - P.P1) * P.m + P.cR) :
    (∀ e, ((P.P1 * u + (1 - P.P1) * P.m + P.cR) / 2 - P.P1 * u) / (1 - P.P1) < e → e ≤ P.m →
        P.IsBestResponseR 1 u ((P.P1 * u + (1 - P.P1) * P.m + P.cR) / 2) e) ∧
    ((2 - P.P1) * u < (1 - P.P1) * P.m + P.cR → ∀ r e, P.IsBestResponseR 1 u r e →
        r = (P.P1 * u + (1 - P.P1) * P.m + P.cR) / 2 ∧ (r - P.P1 * u) / (1 - P.P1) < e) := by
  have hP' := hP
  obtain ⟨hm, hp0, hp1, hc0, hcm, hr0, hrm⟩ := hP'
  have hq : 0 < 1 - P.P1 := by linarith
  set η := P.P1 * u + (1 - P.P1) * P.m with hη
  set rs := (η + P.cR) / 2 with hrs
  set V := ((η - P.cR) ^ 2 / 4) / (2 * (1 - P.P1)) with hV
  have hum : u ≤ P.m := by
    have := mul_le_mul_of_nonneg_left hrm hq.le
    nlinarith
  have hηc : (1 - P.P1) * (P.m - P.cR) < η - P.cR := by
    rw [hη]; linarith [mul_lt_mul_of_pos_left hcu hp0]
  have hurs : u ≤ rs := by rw [hrs, hη]; linarith
  have hrsη : rs < η := by
    rw [hrs]
    have : P.cR < η := by have := mul_nonneg hq.le (by linarith : (0:ℝ) ≤ P.m - P.cR); linarith
    linarith
  -- contingent maximum is strictly below V
  have hIV : (1 - P.P1) * (P.m - P.cR) ^ 2 / 8 < V := by
    have hx : 0 ≤ (1 - P.P1) * (P.m - P.cR) := mul_nonneg hq.le (by linarith)
    have hsq := mul_self_lt_mul_self hx hηc
    rw [hV, div_div, lt_div_iff₀ (by positivity)]
    nlinarith
  have bound : ∀ r e, P.RFeasible r e → Rf P u r e ≤ V := by
    intro r e ⟨g1, g2, g3⟩
    unfold Rf
    split_ifs with k1 k2
    · refine (RIV_le_RM P hP u r g1 k1).trans ?_
      rw [RM_vertex P hq, hV]
      apply div_le_div_of_nonneg_right _ (by linarith)
      rw [← hη]; nlinarith [sq_nonneg (r - (η + P.cR) / 2)]
    · rw [RI_vertex]
      have := mul_nonneg hq.le (sq_nonneg (e - (P.m + P.cR) / 2))
      linarith
    · rw [RM_vertex P hq, hV]
      apply div_le_div_of_nonneg_right _ (by linarith)
      rw [← hη]; nlinarith [sq_nonneg (r - (η + P.cR) / 2)]
  have hRMrs : (rs - P.cR) * (((1 - P.P1) * P.m - rs + P.P1 * u) / (2 * (1 - P.P1))) = V := by
    rw [RM_vertex P hq, hV, ← hη, hrs]; ring
  have attain : ∀ e, (rs - P.P1 * u) / (1 - P.P1) < e → Rf P u rs e = V := by
    intro e he
    rw [div_lt_iff₀ hq] at he
    rcases hurs.lt_or_eq with hlt | heq
    · rw [Rf_M P _ _ _ hlt (by linarith)]; exact hRMrs
    · rw [Rf_IV P _ _ _ heq.ge, ← hRMrs, ← heq]
      exact (RM_at_u P hq u).symm
  have hfeas : ∀ e, (rs - P.P1 * u) / (1 - P.P1) < e → e ≤ P.m → P.RFeasible rs e := by
    intro e he1 he2
    rw [div_lt_iff₀ hq] at he1
    refine ⟨by linarith, ?_, he2⟩
    have := mul_le_mul_of_nonneg_left hurs hp0.le
    have : (1 - P.P1) * rs < (1 - P.P1) * e := by linarith
    exact (lt_of_mul_lt_mul_left this hq.le).le
  refine ⟨fun e he1 he2 => BR_of P u rs e V (hfeas e he1 he2) (attain e he1) bound, ?_⟩
  intro hlt r e hBR
  have hlt' : u < rs := by rw [hrs, hη]; linarith
  have hm0 : (rs - P.P1 * u) / (1 - P.P1) < P.m := by rw [div_lt_iff₀ hq]; linarith
  have hv := BR_val P u r e V rs P.m hBR (hfeas P.m hm0 le_rfl) (attain P.m hm0) bound
  obtain ⟨g1, g2, g3⟩ := hBR.1
  unfold Rf at hv
  split_ifs at hv with k1 k2
  · exfalso
    have h1 := RIV_le_RM P hP u r g1 k1
    rw [RM_vertex P hq, ← hη] at h1
    have : 0 < (r - (η + P.cR) / 2) ^ 2 := by
      have : r - (η + P.cR) / 2 ≠ 0 := by rw [← hrs]; linarith
      positivity
    have h2 : ((η - P.cR) ^ 2 / 4 - (r - (η + P.cR) / 2) ^ 2) / (2 * (1 - P.P1)) < V := by
      rw [hV]; apply div_lt_div_of_pos_right _ (by linarith); linarith
    linarith
  · exfalso
    rw [RI_vertex] at hv
    have := mul_nonneg hq.le (sq_nonneg (e - (P.m + P.cR) / 2))
    linarith
  · push_neg at k1 k2
    rw [RM_vertex P hq, hV, ← hη] at hv
    have h0 : (r - (η + P.cR) / 2) ^ 2 = 0 := by
      rw [div_left_inj' (by linarith : (2 * (1 - P.P1)) ≠ 0)] at hv
      linarith
    have hr : r = rs := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0
      rw [hrs]; linarith
    refine ⟨hr, ?_⟩
    rw [div_lt_iff₀ hq]; linarith

lemma case_iv (P : Params) (hP : P.Standing) (u : ℝ) (hu : u ≤ P.cR) :
    (∀ r, (1 - P.P1) * ((P.m + P.cR) / 2) + P.P1 * u ≤ r → P.cR ≤ r → r ≤ (P.m + P.cR) / 2 →
        P.IsBestResponseR 1 u r ((P.m + P.cR) / 2)) ∧
    (u < P.cR → ∀ r e, P.IsBestResponseR 1 u r e →
        e = (P.m + P.cR) / 2 ∧ (1 - P.P1) * e + P.P1 * u ≤ r) := by
  have hP' := hP
  obtain ⟨hm, hp0, hp1, hc0, hcm, hr0, hrm⟩ := hP'
  have hq : 0 < 1 - P.P1 := by linarith
  set V := (1 - P.P1) * (P.m - P.cR) ^ 2 / 8 with hV
  have hV0 : 0 ≤ V := by positivity
  have hRM : ∀ r, (r - P.cR) * (((1 - P.P1) * P.m - r + P.P1 * u) / (2 * (1 - P.P1))) ≤
      ((P.P1 * u + (1 - P.P1) * P.m - P.cR) ^ 2 / 4) / (2 * (1 - P.P1)) := by
    intro r
    rw [RM_vertex P hq]
    apply div_le_div_of_nonneg_right _ (by linarith)
    nlinarith [sq_nonneg (r - (P.P1 * u + (1 - P.P1) * P.m + P.cR) / 2)]
  have bound : ∀ r e, P.RFeasible r e → Rf P u r e ≤ V := by
    intro r e ⟨g1, g2, g3⟩
    unfold Rf
    split_ifs with k1 k2
    · have : r - P.cR ≤ 0 := by linarith
      have := mul_nonpos_of_nonpos_of_nonneg this (by linarith : (0:ℝ) ≤ (P.m - r) / 2)
      linarith
    · rw [RI_vertex]
      have := mul_nonneg hq.le (sq_nonneg (e - (P.m + P.cR) / 2))
      linarith
    · push_neg at k1 k2
      refine (hRM r).trans ?_
      have hx : 0 ≤ P.P1 * u + (1 - P.P1) * P.m - P.cR := by
        nlinarith [mul_le_mul_of_nonneg_left g3 hq.le]
      have hy : P.P1 * u + (1 - P.P1) * P.m - P.cR ≤ (1 - P.P1) * (P.m - P.cR) := by
        nlinarith [mul_le_mul_of_nonneg_left hu hp0.le]
      have hsq := mul_self_le_mul_self hx hy
      rw [hV, div_div, div_le_iff₀ (by positivity)]
      nlinarith
  refine ⟨fun r h1 h2 h3 => ?_, fun hlt r e hBR => ?_⟩
  · apply BR_of P u r _ V ⟨h2, h3, by linarith⟩ _ bound
    rcases lt_or_ge u r with hur | hur
    · rw [Rf_I P _ _ _ hur (by linarith), RI_vertex]; ring
    · -- r ≤ u ≤ c_R ≤ r forces r = u = c_R, and then m = c_R
      have hr : r = P.cR := by linarith
      have hcm' : P.cR = P.m := by
        have hu' : u = P.cR := by linarith
        rw [hu'] at h1
        have : (1 - P.P1) * ((P.m + P.cR) / 2) ≤ (1 - P.P1) * P.cR := by linarith
        have := le_of_mul_le_mul_left this hq
        linarith
      rw [Rf_IV P _ _ _ hur, hr, hV, hcm']; ring
  · -- an attained value: (e', e') with e' = (m + c_R)/2
    set e' := (P.m + P.cR) / 2 with he'
    have hue : u < e' := by linarith
    have hreg : P.P1 * u + (1 - P.P1) * e' ≤ e' := by
      have := mul_le_mul_of_nonneg_left hue.le hp0.le; linarith
    have hatt : Rf P u e' e' = V := by rw [Rf_I P _ _ _ hue hreg, RI_vertex]; ring
    have hv := BR_val P u r e V e' e' hBR ⟨by linarith, le_rfl, by linarith⟩ hatt bound
    obtain ⟨g1, g2, g3⟩ := hBR.1
    unfold Rf at hv
    split_ifs at hv with k1 k2
    · exfalso; linarith
    · rw [RI_vertex] at hv
      have h0 : (1 - P.P1) * (e - e') ^ 2 = 0 := by rw [he']; linarith
      rcases mul_eq_zero.mp h0 with h | h
      · linarith
      · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
        refine ⟨by linarith, by linarith⟩
    · exfalso
      push_neg at k1 k2
      have h1 := hRM r
      have hx : 0 < P.P1 * u + (1 - P.P1) * P.m - P.cR := by
        nlinarith [mul_le_mul_of_nonneg_left g3 hq.le]
      have hy : P.P1 * u + (1 - P.P1) * P.m - P.cR < (1 - P.P1) * (P.m - P.cR) := by
        nlinarith [mul_lt_mul_of_pos_left hlt hp0]
      have hsq := mul_self_lt_mul_self hx.le hy
      have : ((P.P1 * u + (1 - P.P1) * P.m - P.cR) ^ 2 / 4) / (2 * (1 - P.P1)) < V := by
        rw [hV, div_div, div_lt_iff₀ (by positivity)]
        nlinarith
      linarith

end CSLA1

open CSLA1 in
theorem solution (P : Params) (hP : P.Standing) (wU : ℝ) (hwU : P.UFeasible wU) :
    ((P.m + P.cR) / 2 < wU →
      (∀ wE, (P.m + P.cR) / 2 ≤ wE → wE ≤ P.m →
        P.IsBestResponseR 1 wU ((P.m + P.cR) / 2) wE) ∧
      (∀ wR wE, P.IsBestResponseR 1 wU wR wE → wR = (P.m + P.cR) / 2)) ∧
    ((P.P0 * P.m + P.cR) / (P.P0 + 1) < wU → wU ≤ (P.m + P.cR) / 2 →
      (∀ wE, wU ≤ wE → wE ≤ P.m → P.IsBestResponseR 1 wU wU wE) ∧
      (∀ wR wE, P.IsBestResponseR 1 wU wR wE → wR = wU)) ∧
    (P.cR < wU → wU ≤ (P.P0 * P.m + P.cR) / (P.P0 + 1) →
      (∀ wE, ((P.P1 * wU + P.P0 * P.m + P.cR) / 2 - P.P1 * wU) / P.P0 < wE → wE ≤ P.m →
        P.IsBestResponseR 1 wU ((P.P1 * wU + P.P0 * P.m + P.cR) / 2) wE) ∧
      (wU < (P.P0 * P.m + P.cR) / (P.P0 + 1) → ∀ wR wE, P.IsBestResponseR 1 wU wR wE →
        wR = (P.P1 * wU + P.P0 * P.m + P.cR) / 2 ∧ (wR - P.P1 * wU) / P.P0 < wE)) ∧
    (wU ≤ P.cR →
      (∀ wR, P.P0 * ((P.m + P.cR) / 2) + P.P1 * wU ≤ wR → P.cR ≤ wR →
        wR ≤ (P.m + P.cR) / 2 → P.IsBestResponseR 1 wU wR ((P.m + P.cR) / 2)) ∧
      (wU < P.cR → ∀ wR wE, P.IsBestResponseR 1 wU wR wE →
        wE = (P.m + P.cR) / 2 ∧ P.P0 * wE + P.P1 * wU ≤ wR)) := by
  have hp1 := hP.2.2.1
  have h2p : (0:ℝ) < 1 - P.P1 + 1 := by linarith
  simp only [Params.P0]
  refine ⟨fun h => case_i P hP wU h hwU.2, fun h1 h2 => ?_, fun h1 h2 => ?_, fun h => ?_⟩
  · rw [div_lt_iff₀ h2p] at h1
    exact case_ii P hP wU (by linarith) h2
  · rw [le_div_iff₀ h2p] at h2
    obtain ⟨a, b⟩ := case_iii P hP wU h1 (by linarith)
    refine ⟨a, fun hlt => b ?_⟩
    rw [lt_div_iff₀ h2p] at hlt; linarith
  · obtain ⟨a, b⟩ := case_iv P hP wU h
    exact ⟨a, b⟩
