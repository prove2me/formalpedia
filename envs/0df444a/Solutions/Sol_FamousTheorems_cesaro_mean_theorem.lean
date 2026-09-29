-- Prove2me | solution 1 for FamousTheorems.cesaro_mean_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:07:49.837226+00:00
-- url     : https://prove2.me/submissions/f507137b-bed5-45ba-a4c3-dd773337dbbd

import Mathlib

theorem solution {u : ℕ → ℝ} {l : ℝ} (h : Filter.Tendsto u Filter.atTop (nhds l)) :
    Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, u i) Filter.atTop (nhds l) :=
  h.cesaro
