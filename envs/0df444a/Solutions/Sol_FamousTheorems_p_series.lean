-- Prove2me | solution 1 for FamousTheorems.p_series
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T07:15:02.687074+00:00
-- url     : https://prove2.me/submissions/d876f559-dcec-458f-b562-5a61c69fbfad

import Mathlib

universe u v

open Filter Set Topology DirectSum

theorem solution {p : ℝ} : Summable (fun n => 1 / (n : ℝ) ^ p : ℕ → ℝ) ↔ 1 < p :=
  Real.summable_one_div_nat_rpow
