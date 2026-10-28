-- Prove2me | solution 1 for AvramDividend.Classical.chat04_exponential_density_rate_shift_ws01a
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T17:59:55.243989+00:00
-- url     : https://prove2.me/submissions/f98bf87e-5b59-4550-bdcc-fc5c79e79f97

import Mathlib.Probability.Distributions.Exponential
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ProbabilityTheory Classical
open scoped ENNReal

/-- Discounting an exponential observation density changes its rate. -/
theorem solution (p q t : ℝ) (hp : 0 < p) (hq : 0 ≤ q) :
    ENNReal.ofReal (p + q) * ProbabilityTheory.exponentialPDF p t *
      ENNReal.ofReal (Real.exp (-(q * t))) =
    ENNReal.ofReal p * ProbabilityTheory.exponentialPDF (p + q) t := by
  by_cases ht : 0 ≤ t
  · rw [ProbabilityTheory.exponentialPDF_of_nonneg ht,
        ProbabilityTheory.exponentialPDF_of_nonneg ht]
    have hpq : 0 ≤ p + q := by linarith
    have hprod : 0 ≤ (p + q) * (p * Real.exp (-(p * t))) :=
      mul_nonneg hpq (mul_nonneg hp.le (Real.exp_pos _).le)
    rw [← ENNReal.ofReal_mul hpq,
        ← ENNReal.ofReal_mul hprod,
        ← ENNReal.ofReal_mul hp.le]
    congr 1
    have he : Real.exp (-(p * t)) * Real.exp (-(q * t)) =
        Real.exp (-((p + q) * t)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      (p + q) * (p * Real.exp (-(p * t))) *
          Real.exp (-(q * t)) =
        (p + q) * p *
          (Real.exp (-(p * t)) * Real.exp (-(q * t))) := by ring
      _ = (p + q) * p * Real.exp (-((p + q) * t)) := by rw [he]
      _ = p * ((p + q) * Real.exp (-((p + q) * t))) := by ring
  · have hn : t < 0 := lt_of_not_ge ht
    simp [ProbabilityTheory.exponentialPDF_of_neg hn]
