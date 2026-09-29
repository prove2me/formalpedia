-- Prove2me | solution 1 for FamousTheorems.monotone_convergence_bounded_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:17:57.671985+00:00
-- url     : https://prove2.me/submissions/764eb2f6-b7fb-4de3-9c49-80b3b66462ec

import Mathlib

theorem solution {f : ℕ → ℝ} (hf : Monotone f) (hbdd : BddAbove (Set.range f)) :
    Filter.Tendsto f Filter.atTop (nhds (⨆ i, f i)) :=
  tendsto_atTop_ciSup hf hbdd
