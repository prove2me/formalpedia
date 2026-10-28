-- Prove2me | solution 1 for AvramDividend.Classical.positive_mgf_eq_implies_tilt_complexMGF_real_ray
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T18:09:10.073461+00:00
-- url     : https://prove2.me/submissions/40124b73-8bc3-4cee-9ba6-5e2a4ae920cd

import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_exp_tilt_real_mgf_shift

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem solution
    (μ ν : Measure ℝ)
    (hm : ∀ u : ℝ, 0 < u →
      (∫ x, Real.exp (u * x) ∂μ) = (∫ x, Real.exp (u * x) ∂ν))
    (s : ℝ) (hs : -1 < s) :
    complexMGF id (μ.withDensity
      (fun x : ℝ => ENNReal.ofReal (Real.exp x))) (s : ℂ) =
    complexMGF id (ν.withDensity
      (fun x : ℝ => ENNReal.ofReal (Real.exp x))) (s : ℂ) := by
  have hμ := exp_tilt_real_mgf_shift μ 1 s
  have hν := exp_tilt_real_mgf_shift ν 1 s
  simp only [one_mul] at hμ hν
  have hreal : (∫ x, Real.exp (s * x) ∂(μ.withDensity
      (fun x : ℝ => ENNReal.ofReal (Real.exp x)))) =
    (∫ x, Real.exp (s * x) ∂(ν.withDensity
      (fun x : ℝ => ENNReal.ofReal (Real.exp x)))) := by
    rw [hμ, hν]
    exact hm (1 + s) (by linarith)
  simpa only [complexMGF_ofReal, mgf, id_eq] using
    congrArg (fun r : ℝ => (r : ℂ)) hreal