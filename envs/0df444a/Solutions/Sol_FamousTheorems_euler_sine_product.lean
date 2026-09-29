-- Prove2me | solution 1 for FamousTheorems.euler_sine_product
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:21:17.704299+00:00
-- url     : https://prove2.me/submissions/04ae9009-75f4-42cc-ac85-de0aeb86e3f3

import Mathlib

theorem solution (z : ℂ) :
    Filter.Tendsto (fun n : ℕ => (Real.pi : ℂ) * z * ∏ j ∈ Finset.range n, (1 - z ^ 2 / ((j : ℂ) + 1) ^ 2))
      Filter.atTop (nhds (Complex.sin ((Real.pi : ℂ) * z))) :=
  Complex.tendsto_euler_sin_prod z
