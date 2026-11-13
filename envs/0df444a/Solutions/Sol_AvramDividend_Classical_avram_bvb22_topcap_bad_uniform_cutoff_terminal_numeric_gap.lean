-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb22_topcap_bad_uniform_cutoff_terminal_numeric_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T00:14:40.215283+00:00
-- url     : https://prove2.me/submissions/49d07aca-8d3e-4716-9899-88602e7cb35c

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical Real
noncomputable section

theorem solution :
    (1 : ℝ) + (1 / 20) * (1 + (3 / 4) * (1 / 20)) <
      (47 / 40) * Real.exp (-(1 : ℝ) / 10) := by
  have h := Real.add_one_le_exp (-(1 : ℝ) / 10)
  nlinarith
