-- Prove2me | solution 1 for FamousTheorems.cauchy_estimate
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:17:59.947368+00:00
-- url     : https://prove2.me/submissions/615b9fb1-4ed1-4422-b4a6-47c265ff6825

import Mathlib

theorem solution {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {c : ℂ} {R C : ℝ} {f : ℂ → F} (hR : 0 < R)
    (hd : DiffContOnCl ℂ f (Metric.ball c R)) (hC : ∀ z ∈ Metric.sphere c R, ‖f z‖ ≤ C) : ‖deriv f c‖ ≤ C / R :=
  Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hd hC
