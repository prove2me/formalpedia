-- Prove2me | solution 1 for FamousTheorems.leibniz_series_pi
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T21:55:59.12793+00:00
-- url     : https://prove2.me/submissions/d8857cdf-6030-4e5c-b4bd-854f3fa85564

import Mathlib

theorem solution : Filter.Tendsto (fun k : ℕ => ∑ i ∈ Finset.range k, ((-1) ^ i / (2 * (i : ℝ) + 1)))
      Filter.atTop (nhds (Real.pi / 4)) :=
  Real.tendsto_sum_pi_div_four
