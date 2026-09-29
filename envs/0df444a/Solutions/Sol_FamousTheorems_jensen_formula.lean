-- Prove2me | solution 1 for FamousTheorems.jensen_formula
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:26:51.804387+00:00
-- url     : https://prove2.me/submissions/cf016d08-7b4e-4cc3-b76d-9c2f079e22bc

import Mathlib

theorem solution {c : ℂ} {R : ℝ} {f : ℂ → ℂ} (hR : R ≠ 0) (h₁f : MeromorphicOn f (Metric.closedBall c |R|)) :
    Real.circleAverage (fun z => Real.log ‖f z‖) c R =
      ∑ᶠ u, (MeromorphicOn.divisor f (Metric.closedBall c |R|) u : ℝ) * Real.log (R * ‖c - u‖⁻¹) +
        (MeromorphicOn.divisor f (Metric.closedBall c |R|) c : ℝ) * Real.log R +
        Real.log ‖meromorphicTrailingCoeffAt f c‖ :=
  MeromorphicOn.circleAverage_log_norm hR h₁f
