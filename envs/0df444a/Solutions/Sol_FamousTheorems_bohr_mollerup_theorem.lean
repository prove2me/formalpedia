-- Prove2me | solution 1 for FamousTheorems.bohr_mollerup_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:02:10.642274+00:00
-- url     : https://prove2.me/submissions/d88c6d9a-4b6d-4850-92df-8dd884d37e59

import Mathlib

theorem solution {f : ℝ → ℝ} (hf_conv : ConvexOn ℝ (Set.Ioi 0) (Real.log ∘ f)) (hf_feq : ∀ {y : ℝ}, 0 < y → f (y + 1) = y * f y)
    (hf_pos : ∀ {y : ℝ}, 0 < y → 0 < f y) (hf_one : f 1 = 1) : Set.EqOn f Real.Gamma (Set.Ioi 0) :=
  Real.eq_Gamma_of_log_convex hf_conv hf_feq hf_pos hf_one
