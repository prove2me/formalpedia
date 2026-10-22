-- Prove2me | solution 1 for GDPRDataMarkets.Benchmark.eq8_no_second_period
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:22:11.763512+00:00
-- url     : https://prove2.me/submissions/1aea3298-4209-4afc-a8e1-1bdc2088d4fe

import Mathlib
import Definitions.Def_GDPRDataMarkets_Benchmark_Model
import Definitions.Def_GDPRDataMarkets_Benchmark_Reduced
set_option autoImplicit false
open MeasureTheory
open GDPRDataMarkets.Benchmark

theorem solution (P : Params) (hS : P.Standing) :
    (∀ (σ : Profile) (p1 v : ℝ), 0 ≤ v → σ.r v = (1 + P.mu - P.sigma) * v →
        (0 ≤ U1buy P σ p1 v ↔ vN P p1 ≤ v)) ∧
    (∀ p1 : ℝ, piN P p1 ≤ piN P (p8 P)) := by
  obtain ⟨hL, hLH, hd0, hd1, hc0⟩ := hS
  have hσ : 0 < P.sigma := by unfold Params.sigma; linarith
  have hμσ : P.sigma < P.mu := by unfold Params.mu Params.sigma; linarith
  have hμ : 0 < P.mu := by linarith
  have hG : 0 < 1 + P.d * P.sigma := by nlinarith [mul_pos hd0 hσ]
  have hF : 0 < 2 + P.d + P.d * P.mu + P.d * P.sigma := by
    nlinarith [mul_pos hd0 hσ, mul_pos hd0 hμ]
  have hG' := hG.ne'
  have hF' := hF.ne'
  have hmusig : P.mu - P.sigma = P.kL := by unfold Params.mu Params.sigma; ring
  have hmusig' : P.mu + P.sigma = P.kH := by unfold Params.mu Params.sigma; ring
  refine ⟨?_, ?_⟩
  · intro σ p1 v hv hr
    have hU : U1buy P σ p1 v = (1 + P.d * P.sigma) * v - p1 - (1 + P.d) * P.c := by
      unfold U1buy u2B
      rw [hr]
      have e1 : (1 + P.kL) * v - (1 + P.mu - P.sigma) * v - P.c = -P.c := by
        have : 1 + P.mu - P.sigma = 1 + P.kL := by linarith
        rw [this]; ring
      have e2 : (1 + P.kH) * v - (1 + P.mu - P.sigma) * v - P.c = 2 * P.sigma * v - P.c := by
        have : 1 + P.mu - P.sigma = 1 + P.kL := by linarith
        rw [this]
        have : P.kH - P.kL = 2 * P.sigma := by unfold Params.sigma; ring
        nlinarith
      rw [e1, e2, max_self, max_eq_left (by nlinarith)]
      ring
    rw [hU]
    unfold vN
    rw [div_le_iff₀ hG]
    constructor <;> intro h <;> nlinarith
  · have hI : ∀ p : ℝ, ∫ v in (vN P p)..1, (p + P.d * ((1 + P.mu - P.sigma) * v)) =
        (1 - vN P p) * p + P.d * (1 + P.mu - P.sigma) * ((1 ^ 2 - (vN P p) ^ 2) / 2) := by
      intro p
      rw [intervalIntegral.integral_add (by simp) (by apply Continuous.intervalIntegrable; fun_prop),
        intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul, integral_id]
      simp only [smul_eq_mul]
      ring
    have key : ∀ p : ℝ, piN P (p8 P) - piN P p =
        (2 + P.d + P.d * P.mu + P.d * P.sigma) / (2 * (1 + P.d * P.sigma) ^ 2) *
          (p - p8 P) ^ 2 := by
      intro p
      unfold piN
      rw [hI, hI]
      unfold vN p8
      field_simp
      ring
    intro p1
    have := key p1
    have hnn : 0 ≤ (2 + P.d + P.d * P.mu + P.d * P.sigma) / (2 * (1 + P.d * P.sigma) ^ 2) *
          (p1 - p8 P) ^ 2 := by positivity
    linarith
