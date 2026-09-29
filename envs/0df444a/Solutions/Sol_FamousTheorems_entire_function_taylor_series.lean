-- Prove2me | solution 1 for FamousTheorems.entire_function_taylor_series
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:23:02.06089+00:00
-- url     : https://prove2.me/submissions/f068a39e-d101-4f54-828e-be62699fd74d

import Mathlib

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E}
    (hf : Differentiable ℂ f) (c z : ℂ) :
    HasSum (fun n : ℕ => ((n.factorial : ℂ))⁻¹ • (z - c) ^ n • iteratedDeriv n f c) (f z) :=
  Complex.hasSum_taylorSeries_of_entire hf c z
