-- Prove2me | solution 1 for FamousTheorems.lebesgue_monotone_differentiation_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:50:36.033087+00:00
-- url     : https://prove2.me/submissions/94f1087d-3ac8-4fbc-9e1d-38330cb3bf72

import Mathlib

open MeasureTheory

theorem solution {f : ℝ → ℝ} (hf : Monotone f) : ∀ᵐ x ∂volume, DifferentiableAt ℝ f x :=
  hf.ae_differentiableAt
