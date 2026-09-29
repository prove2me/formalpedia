-- Prove2me | solution 1 for FamousTheorems.geom_mean_le_arith_mean_weighted
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T22:17:24.789665+00:00
-- url     : https://prove2.me/submissions/60328393-19c3-481a-8aaf-d5b6c0f51abc

import Mathlib

theorem solution : ∀ {ι : Type*} (s : Finset ι) (w z : ι → ℝ), (∀ i ∈ s, 0 ≤ w i) →
    ∑ i ∈ s, w i = 1 → (∀ i ∈ s, 0 ≤ z i) →
    ∏ i ∈ s, z i ^ w i ≤ ∑ i ∈ s, w i * z i :=
  Real.geom_mean_le_arith_mean_weighted
