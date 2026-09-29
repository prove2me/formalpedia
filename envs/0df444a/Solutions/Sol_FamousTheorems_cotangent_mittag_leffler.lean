-- Prove2me | solution 1 for FamousTheorems.cotangent_mittag_leffler
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:21:30.045795+00:00
-- url     : https://prove2.me/submissions/7509a301-4572-45e3-9a67-131f8dbae282

import Mathlib

theorem solution {x : ℂ} (hx : x ∈ Complex.integerComplement) :
    (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * x) = 1 / x + ∑' n : ℕ+, (1 / (x - ((n : ℕ) : ℂ)) + 1 / (x + ((n : ℕ) : ℂ))) :=
  cot_series_rep hx
