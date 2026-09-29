-- Prove2me | solution 1 for FamousTheorems.harmonic_series_diverges
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T21:55:58.906627+00:00
-- url     : https://prove2.me/submissions/7b0950ed-636c-4ce6-9e1b-bb950bb2370a

import Mathlib

theorem solution : Filter.Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 1))
      Filter.atTop Filter.atTop :=
  Real.tendsto_sum_range_one_div_nat_succ_atTop
