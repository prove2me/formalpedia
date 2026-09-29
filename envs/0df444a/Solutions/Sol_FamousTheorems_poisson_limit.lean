-- Prove2me | solution 1 for FamousTheorems.poisson_limit
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:21:06.677176+00:00
-- url     : https://prove2.me/submissions/2c1c6872-02ac-45c3-b7cd-aedb0827e9c3

import Mathlib

theorem solution {p : ℕ → ℝ} {r : ℝ} (k : ℕ) (hr : Filter.Tendsto (fun n : ℕ => (n : ℝ) * p n) Filter.atTop (nhds r)) :
    Filter.Tendsto (fun n : ℕ => ((n.choose k : ℕ) : ℝ) * p n ^ k * (1 - p n) ^ (n - k)) Filter.atTop
      (nhds (Real.exp (-r) * r ^ k / (k.factorial : ℝ))) :=
  ProbabilityTheory.tendsto_choose_mul_pow_of_tendsto_mul_atTop k hr
