-- Prove2me | solution 1 for FamousTheorems.riemann_zeta_laurent_euler_mascheroni_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:07:57.979593+00:00
-- url     : https://prove2.me/submissions/bbad66e1-d4d4-4709-b40a-9749a1817359

import Mathlib

theorem solution : Filter.Tendsto (fun s : ℂ => riemannZeta s - 1 / (s - 1)) (nhdsWithin 1 {1}ᶜ)
    (nhds (Real.eulerMascheroniConstant : ℂ)) :=
  tendsto_riemannZeta_sub_one_div
