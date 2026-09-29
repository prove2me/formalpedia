-- Prove2me | solution 1 for FamousTheorems.cauchy_condensation_test
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:07:47.891793+00:00
-- url     : https://prove2.me/submissions/6b0ace40-48ab-474e-aab5-b03f2ecd5946

import Mathlib

theorem solution {f : ℕ → ℝ} (h_nonneg : ∀ n, 0 ≤ f n) (h_mono : ∀ ⦃m n : ℕ⦄, 0 < m → m ≤ n → f n ≤ f m) :
    (Summable fun k : ℕ => 2 ^ k * f (2 ^ k)) ↔ Summable f :=
  summable_condensed_iff_of_nonneg h_nonneg h_mono
