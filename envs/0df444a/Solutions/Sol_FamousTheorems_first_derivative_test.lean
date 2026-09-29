-- Prove2me | solution 1 for FamousTheorems.first_derivative_test
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:49:17.958368+00:00
-- url     : https://prove2.me/submissions/dfef86b8-1c84-4c75-b66d-ef7452701931

import Mathlib

theorem solution {f : ℝ → ℝ} {x₀ : ℝ} (hc : ContinuousAt f x₀)
    (hs : ∀ᶠ x in nhdsWithin x₀ {x₀}ᶜ, SignType.sign (deriv f x) = SignType.sign (x₀ - x)) :
    IsLocalMax f x₀ :=
  isLocalMax_of_sign_deriv hc hs
