-- Prove2me | solution 1 for FamousTheorems.second_derivative_test
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:48:30.975138+00:00
-- url     : https://prove2.me/submissions/04de89a1-e58d-441a-861a-0dfd11c18bb3

import Mathlib

theorem solution {f : ℝ → ℝ} {x₀ : ℝ} (hf : deriv (deriv f) x₀ > 0) (hd : deriv f x₀ = 0) (hc : ContinuousAt f x₀) :
    IsLocalMin f x₀ :=
  isLocalMin_of_deriv_deriv_pos hf hd hc
