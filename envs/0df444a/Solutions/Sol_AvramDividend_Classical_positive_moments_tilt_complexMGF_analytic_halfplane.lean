-- Prove2me | solution 1 for AvramDividend.Classical.positive_moments_tilt_complexMGF_analytic_halfplane
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T18:56:45.539135+00:00
-- url     : https://prove2.me/submissions/87bea44a-cf10-4b77-9e0e-0be1a77486d9

import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Topology.Sets.Opens
import Theorems.Thm_AvramDividend_Classical_pos_moments_exp_tilt_integrable_right_ray

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem solution
    (μ : Measure ℝ)
    (h : ∀ u : ℝ, 0 < u →
      Integrable (fun x : ℝ => Real.exp (u * x)) μ) :
    AnalyticOnNhd ℂ (complexMGF id
      (μ.withDensity (fun x : ℝ => ENNReal.ofReal (Real.exp x))))
      {z : ℂ | -1 < z.re} := by
  let μt : Measure ℝ :=
    μ.withDensity (fun x : ℝ => ENNReal.ofReal (Real.exp x))
  have hs : Set.Ioi (-1 : ℝ) ⊆ integrableExpSet id μt := by
    intro t ht
    exact pos_moments_exp_tilt_integrable_right_ray μ h t ht
  have hi : Set.Ioi (-1 : ℝ) ⊆ interior (integrableExpSet id μt) :=
    interior_maximal hs isOpen_Ioi
  exact (analyticOnNhd_complexMGF (X := id) (μ := μt)).mono
    (by intro z hz; exact hi hz)