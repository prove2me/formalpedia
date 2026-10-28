-- Prove2me | solution 1 for AvramDividend.Classical.chat04_exponential_discount_rate_shift_lintegral_ws01a
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T18:01:37.95948+00:00
-- url     : https://prove2.me/submissions/1ae46dbd-56dd-42ed-a280-1cd053449d0c

import Mathlib.Probability.Distributions.Exponential
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ProbabilityTheory Classical MeasureTheory
open scoped ENNReal

/-- Discounting an exponential observation density changes its rate. -/
private theorem exp_density_shift (p q t : ℝ) (hp : 0 < p) (hq : 0 ≤ q) :
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

/-- Equality of the actual nonnegative rate-shifted exponential-clock integrals. -/
theorem solution (p q : ℝ) (hp : 0 < p) (hq : 0 ≤ q)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ENNReal.ofReal (p + q) *
      (∫⁻ t : ℝ, ProbabilityTheory.exponentialPDF p t *
        ENNReal.ofReal (Real.exp (-(q * t))) * f t ∂volume) =
    ENNReal.ofReal p *
      (∫⁻ t : ℝ, ProbabilityTheory.exponentialPDF (p + q) t *
        f t ∂volume) := by
  have hpdfP : Measurable (ProbabilityTheory.exponentialPDF p) :=
    (ProbabilityTheory.measurable_exponentialPDFReal p).ennreal_ofReal
  have hpdfR : Measurable (ProbabilityTheory.exponentialPDF (p + q)) :=
    (ProbabilityTheory.measurable_exponentialPDFReal (p + q)).ennreal_ofReal
  have hExpReal : Measurable (fun t : ℝ => Real.exp (-(q * t))) :=
    Real.continuous_exp.measurable.comp
      ((measurable_const.mul measurable_id).neg)
  have hExp : Measurable (fun t : ℝ =>
      ENNReal.ofReal (Real.exp (-(q * t)))) := hExpReal.ennreal_ofReal
  have hL : Measurable (fun t : ℝ =>
      ProbabilityTheory.exponentialPDF p t *
        ENNReal.ofReal (Real.exp (-(q * t))) * f t) :=
    (hpdfP.mul hExp).mul hf
  have hR : Measurable (fun t : ℝ =>
      ProbabilityTheory.exponentialPDF (p + q) t * f t) :=
    hpdfR.mul hf
  rw [← lintegral_const_mul, ← lintegral_const_mul]
  apply lintegral_congr
  intro t
  calc
    ENNReal.ofReal (p + q) *
        (ProbabilityTheory.exponentialPDF p t *
          ENNReal.ofReal (Real.exp (-(q * t))) * f t) =
      (ENNReal.ofReal (p + q) * ProbabilityTheory.exponentialPDF p t *
        ENNReal.ofReal (Real.exp (-(q * t)))) * f t := by ac_rfl
    _ = (ENNReal.ofReal p * ProbabilityTheory.exponentialPDF (p + q) t) *
        f t := by rw [exp_density_shift p q t hp hq]
    _ = ENNReal.ofReal p * (ProbabilityTheory.exponentialPDF (p + q) t * f t) := by
      ac_rfl
  all_goals first | exact hR | exact hL
