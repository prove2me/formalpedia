-- Prove2me | solution 1 for GDPRDataMarkets.Benchmark.corner_regime
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:25:20.118015+00:00
-- url     : https://prove2.me/submissions/8eae2996-eddb-4b52-98f4-3363933f78a6

import Mathlib
import Definitions.Def_GDPRDataMarkets_Benchmark_Model
import Definitions.Def_GDPRDataMarkets_Benchmark_Reduced
set_option autoImplicit false
open MeasureTheory
open GDPRDataMarkets.Benchmark

lemma fg_sq_aux (p1 a m : ℝ) (h1 : p1 ≤ a) (h2 : a ≤ m) : (a - m) ^ 2 ≤ (p1 - m) ^ 2 := by
  nlinarith

lemma fg_sq_aux2 (p1 a m : ℝ) (h1 : a ≤ p1) (h2 : m ≤ a) : (a - m) ^ 2 ≤ (p1 - m) ^ 2 := by
  nlinarith

theorem solution (P : Params) (hS : P.Standing) :
    vN P (P.d * (P.sigma - 1) * P.c) = P.c ∧
    vB P (P.d * (P.sigma - 1) * P.c) = P.c ∧
    (T1 P < P.c → P.c ≤ (1 + P.d * P.sigma) / (1 + P.d * P.mu + P.d * P.sigma) →
      (∀ p1 : ℝ, p1 ≤ P.d * (P.sigma - 1) * P.c →
          piN P p1 ≤ piN P (P.d * (P.sigma - 1) * P.c)) ∧
      (∀ p1 : ℝ, P.d * (P.sigma - 1) * P.c ≤ p1 →
          piS P p1 ≤ piS P (P.d * (P.sigma - 1) * P.c)) ∧
      P2B P = P.d * (P.sigma - 1) * P.c ∧ v2B P = P.c) ∧
    ((1 + P.d * P.sigma) / (1 + P.d * P.mu + P.d * P.sigma) < P.c →
      P2B P = p8 P ∧ v2B P = vN P (p8 P)) := by
  obtain ⟨hL, hLH, hd0, hd1, hc0⟩ := hS
  have hσ : 0 < P.sigma := by unfold Params.sigma; linarith
  have hμσ : P.sigma < P.mu := by unfold Params.mu Params.sigma; linarith
  have hμ : 0 < P.mu := by linarith
  have hD1 : 0 < 2 - P.d + 2 * P.d * P.sigma := by nlinarith [mul_pos hd0 hσ]
  have hE : 0 < 4 - P.d + 2 * P.d * P.mu + 2 * P.d * P.sigma := by
    nlinarith [mul_pos hd0 hσ, mul_pos hd0 hμ]
  have hF : 0 < 2 + P.d + P.d * P.mu + P.d * P.sigma := by
    nlinarith [mul_pos hd0 hσ, mul_pos hd0 hμ]
  have hG : 0 < 1 + P.d * P.sigma := by nlinarith [mul_pos hd0 hσ]
  have hH : 0 < 1 + P.d * P.mu + P.d * P.sigma := by nlinarith [mul_pos hd0 hσ, mul_pos hd0 hμ]
  have hT : 0 < 2 - P.d + 2 * P.d * P.sigma + 2 * P.d * P.mu := by
    nlinarith [mul_pos hd0 hσ, mul_pos hd0 hμ]
  have hdm : 0 < P.d * P.mu := mul_pos hd0 hμ
  have hD1' := hD1.ne'
  have hE' := hE.ne'
  have hF' := hF.ne'
  have hG' := hG.ne'
  have hH' := hH.ne'
  have hT' := hT.ne'
  have h1d : (1 + P.d) ≠ 0 := by positivity
  have hT1 : T1 P = (2 - P.d + 2 * P.d * P.sigma) / (2 - P.d + 2 * P.d * P.sigma + 2 * P.d * P.mu) := by
    unfold T1; congr 1; ring
  -- the corner price
  have hvN : vN P (P.d * (P.sigma - 1) * P.c) = P.c := by
    unfold vN; field_simp; ring
  have hvB : vB P (P.d * (P.sigma - 1) * P.c) = P.c := by
    unfold vB; field_simp; ring
  -- vN (p8) in closed form
  have hvNp8 : vN P (p8 P) = (1 + P.d * P.sigma + (1 + P.d) * P.c) / (2 + P.d + P.d * P.mu + P.d * P.sigma) := by
    unfold vN p8; field_simp; ring
  have hp8c : p8 P - P.d * (P.sigma - 1) * P.c =
      (1 + P.d * P.sigma) * ((1 + P.d * P.sigma) - P.c * (1 + P.d * P.mu + P.d * P.sigma)) /
        (2 + P.d + P.d * P.mu + P.d * P.sigma) := by
    unfold p8; field_simp; ring
  have hv8 : vN P (p8 P) - P.c = ((1 + P.d * P.mu + P.d * P.sigma) / (2 + P.d + P.d * P.mu + P.d * P.sigma)) *
      ((1 + P.d * P.sigma) / (1 + P.d * P.mu + P.d * P.sigma) - P.c) := by
    unfold vN p8; field_simp; ring
  have key1 : vbar1B P - P.c = ((2 - P.d + 2 * P.d * P.sigma + 2 * P.d * P.mu) / (4 - P.d + 2 * P.d * P.mu + 2 * P.d * P.sigma)) * (T1 P - P.c) := by
    rw [hT1]; unfold vbar1B P1B
    field_simp
    ring
  have hP1c : P1B P - P.d * (P.sigma - 1) * P.c = ((2 - P.d + 2 * P.d * P.sigma) / 2) * (vbar1B P - P.c) := by
    unfold vbar1B P1B; field_simp; ring
  have hk1 : 0 < (2 - P.d + 2 * P.d * P.sigma + 2 * P.d * P.mu) / (4 - P.d + 2 * P.d * P.mu + 2 * P.d * P.sigma) := by positivity
  have hk4 : 0 < (1 + P.d * P.mu + P.d * P.sigma) / (2 + P.d + P.d * P.mu + P.d * P.sigma) := by positivity
  -- integrals
  have hIN : ∀ p : ℝ, ∫ v in (vN P p)..1, (p + P.d * ((1 + P.mu - P.sigma) * v)) =
      (1 - vN P p) * p + P.d * (1 + P.mu - P.sigma) * ((1 ^ 2 - (vN P p) ^ 2) / 2) := by
    intro p
    rw [intervalIntegral.integral_add (by simp) (by apply Continuous.intervalIntegrable; fun_prop),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_id]
    simp only [smul_eq_mul]
    ring
  have hIS : ∀ p : ℝ, ∫ v in (vB P p)..1, (p + P.d * ((1 + P.mu - P.sigma) * v)) =
      (1 - vB P p) * p + P.d * (1 + P.mu - P.sigma) * ((1 ^ 2 - (vB P p) ^ 2) / 2) := by
    intro p
    rw [intervalIntegral.integral_add (by simp) (by apply Continuous.intervalIntegrable; fun_prop),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_id]
    simp only [smul_eq_mul]
    ring
  have keyN : ∀ p : ℝ, piN P (p8 P) - piN P p =
      (2 + P.d + P.d * P.mu + P.d * P.sigma) / (2 * (1 + P.d * P.sigma) ^ 2) * (p - p8 P) ^ 2 := by
    intro p
    unfold piN
    rw [hIN, hIN]
    unfold vN p8
    field_simp
    ring
  have keyS : ∀ p : ℝ, piS P (P1B P) - piS P p =
      (4 - P.d + 2 * P.d * P.mu + 2 * P.d * P.sigma) / (2 - P.d + 2 * P.d * P.sigma) ^ 2 *
        (p - P1B P) ^ 2 := by
    intro p
    unfold piS
    rw [hIS, hIS]
    unfold vB qB P1B
    field_simp
    ring
  refine ⟨hvN, hvB, ?_, ?_⟩
  · intro hTc hRc
    have hRc' : P.c * (1 + P.d * P.mu + P.d * P.sigma) ≤ 1 + P.d * P.sigma := by
      rwa [le_div_iff₀ hH] at hRc
    have hp8nn : 0 ≤ p8 P - P.d * (P.sigma - 1) * P.c := by
      rw [hp8c]; apply div_nonneg _ hF.le
      apply mul_nonneg hG.le; linarith
    have hP1neg : P1B P - P.d * (P.sigma - 1) * P.c ≤ 0 := by
      rw [hP1c]
      have h1 : vbar1B P - P.c ≤ 0 := by
        rw [key1]; exact mul_nonpos_of_nonneg_of_nonpos hk1.le (by linarith)
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) h1
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro p1 hp1
      have hA := keyN p1
      have hB := keyN (P.d * (P.sigma - 1) * P.c)
      have hcoef : 0 ≤ (2 + P.d + P.d * P.mu + P.d * P.sigma) / (2 * (1 + P.d * P.sigma) ^ 2) := by positivity
      have hsq : (P.d * (P.sigma - 1) * P.c - p8 P) ^ 2 ≤ (p1 - p8 P) ^ 2 :=
        fg_sq_aux p1 _ _ hp1 (by linarith)
      have := mul_nonneg hcoef (sub_nonneg.mpr hsq)
      rw [mul_sub] at this
      linarith
    · intro p1 hp1
      have hA := keyS p1
      have hB := keyS (P.d * (P.sigma - 1) * P.c)
      have hcoef : 0 ≤ (4 - P.d + 2 * P.d * P.mu + 2 * P.d * P.sigma) / (2 - P.d + 2 * P.d * P.sigma) ^ 2 := by positivity
      have hsq : (P.d * (P.sigma - 1) * P.c - P1B P) ^ 2 ≤ (p1 - P1B P) ^ 2 :=
        fg_sq_aux2 p1 _ _ hp1 (by linarith)
      have := mul_nonneg hcoef (sub_nonneg.mpr hsq)
      rw [mul_sub] at this
      linarith
    · unfold P2B
      change min (p8 P) _ = _
      exact min_eq_right (by linarith)
    · unfold v2B
      have : P.c ≤ (1 + P.d * P.sigma + (1 + P.d) * P.c) / (2 + P.d + P.d * P.mu + P.d * P.sigma) := by
        rw [← hvNp8]
        have : 0 ≤ vN P (p8 P) - P.c := by
          rw [hv8]; exact mul_nonneg hk4.le (by
            have : P.c ≤ (1 + P.d * P.sigma) / (1 + P.d * P.mu + P.d * P.sigma) := hRc
            linarith)
        linarith
      exact min_eq_right this
  · intro hRc
    have h1 : vN P (p8 P) - P.c < 0 := by
      rw [hv8]; exact mul_neg_of_pos_of_neg hk4 (by linarith)
    have hp8nn : p8 P - P.d * (P.sigma - 1) * P.c < 0 := by
      rw [hp8c]
      have hRc' : (1 + P.d * P.sigma) < P.c * (1 + P.d * P.mu + P.d * P.sigma) := by
        rwa [div_lt_iff₀ hH] at hRc
      apply div_neg_of_neg_of_pos _ hF
      apply mul_neg_of_pos_of_neg hG; linarith
    constructor
    · unfold P2B
      change min (p8 P) _ = _
      exact min_eq_left (by linarith)
    · unfold v2B
      rw [← hvNp8]
      exact min_eq_left (by linarith)
