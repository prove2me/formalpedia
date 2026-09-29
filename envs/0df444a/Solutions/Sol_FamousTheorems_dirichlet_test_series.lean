-- Prove2me | solution 1 for FamousTheorems.dirichlet_test_series
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:28:57.021911+00:00
-- url     : https://prove2.me/submissions/09d1d689-0be8-4d77-aa32-2baab00fe7de

import Mathlib

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {b : ℝ} {f : ℕ → ℝ} {z : ℕ → E}
    (hfa : Antitone f) (hf0 : Filter.Tendsto f Filter.atTop (nhds 0))
    (hgb : ∀ n, ‖∑ i ∈ Finset.range n, z i‖ ≤ b) :
    CauchySeq fun n => ∑ i ∈ Finset.range n, f i • z i :=
  hfa.cauchySeq_series_mul_of_tendsto_zero_of_bounded hf0 hgb
