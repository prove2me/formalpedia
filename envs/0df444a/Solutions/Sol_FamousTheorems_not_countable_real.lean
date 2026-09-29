-- Prove2me | solution 1 for FamousTheorems.not_countable_real
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T21:52:36.870043+00:00
-- url     : https://prove2.me/submissions/7e0547a8-a1f6-4e18-8c1d-21e252a4df82

import Mathlib

theorem solution : ¬ (Set.univ : Set ℝ).Countable :=
  Cardinal.not_countable_real
