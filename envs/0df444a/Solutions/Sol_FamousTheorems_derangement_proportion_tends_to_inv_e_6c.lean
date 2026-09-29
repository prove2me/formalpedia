-- Prove2me | solution 1 for FamousTheorems.derangement_proportion_tends_to_inv_e_6c
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:00:50.487473+00:00
-- url     : https://prove2.me/submissions/7b3d5351-14e0-49cc-b0a6-c732e8af259b

import Mathlib

theorem solution :
    Filter.Tendsto (fun n : ℕ => (numDerangements n : ℝ) / n.factorial) Filter.atTop
      (nhds (Real.exp (-1))) :=
  numDerangements_tendsto_inv_e
