-- Prove2me | solution 1 for FamousTheorems.alternating_series_test
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:07:48.539826+00:00
-- url     : https://prove2.me/submissions/b8afae2d-677a-498d-88de-fc47d0e9eb7f

import Mathlib

theorem solution {f : ℕ → ℝ} (hfa : Antitone f) (hf0 : Filter.Tendsto f Filter.atTop (nhds 0)) :
    ∃ l : ℝ, Filter.Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, (-1) ^ i * f i) Filter.atTop (nhds l) :=
  hfa.tendsto_alternating_series_of_tendsto_zero hf0
