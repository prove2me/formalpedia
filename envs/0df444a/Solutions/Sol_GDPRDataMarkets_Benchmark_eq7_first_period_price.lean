-- Prove2me | solution 1 for GDPRDataMarkets.Benchmark.eq7_first_period_price
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:22:07.440814+00:00
-- url     : https://prove2.me/submissions/dbaf2588-eb22-4db6-afdd-795d1286ed66

import Mathlib
import Definitions.Def_GDPRDataMarkets_Benchmark_Model
import Definitions.Def_GDPRDataMarkets_Benchmark_Reduced
set_option autoImplicit false
open MeasureTheory
open GDPRDataMarkets.Benchmark

theorem solution (P : Params) (hS : P.Standing) :
    ∀ p1 : ℝ, piS P p1 ≤ piS P (P1B P) := by
  obtain ⟨hL, hLH, hd0, hd1, hc0⟩ := hS
  have hσ : 0 < P.sigma := by unfold Params.sigma; linarith
  have hμσ : P.sigma < P.mu := by unfold Params.mu Params.sigma; linarith
  have hμ : 0 < P.mu := by linarith
  have hD1 : 0 < 2 - P.d + 2 * P.d * P.sigma := by nlinarith [mul_pos hd0 hσ]
  have hE : 0 < 4 - P.d + 2 * P.d * P.mu + 2 * P.d * P.sigma := by
    nlinarith [mul_pos hd0 hσ, mul_pos hd0 hμ]
  have hD1' := hD1.ne'
  have hE' := hE.ne'
  have hI : ∀ p : ℝ, ∫ v in (vB P p)..1, (p + P.d * ((1 + P.mu - P.sigma) * v)) =
      (1 - vB P p) * p + P.d * (1 + P.mu - P.sigma) * ((1 ^ 2 - (vB P p) ^ 2) / 2) := by
    intro p
    rw [intervalIntegral.integral_add (by simp) (by apply Continuous.intervalIntegrable; fun_prop),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_id]
    simp only [smul_eq_mul]
    ring
  have key : ∀ p : ℝ, piS P (P1B P) - piS P p =
      (4 - P.d + 2 * P.d * P.mu + 2 * P.d * P.sigma) / (2 - P.d + 2 * P.d * P.sigma) ^ 2 *
        (p - P1B P) ^ 2 := by
    intro p
    unfold piS
    rw [hI, hI]
    unfold vB qB P1B
    field_simp
    ring
  intro p1
  have := key p1
  have hnn : 0 ≤ (4 - P.d + 2 * P.d * P.mu + 2 * P.d * P.sigma) / (2 - P.d + 2 * P.d * P.sigma) ^ 2 *
        (p1 - P1B P) ^ 2 := by positivity
  linarith
