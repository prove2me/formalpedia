-- Prove2me | solution 1 for FamousTheorems.kronecker_density_pair_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:54:38.878009+00:00
-- url     : https://prove2.me/submissions/2bba6f56-d39d-44dd-9457-250d1b30e683

import Mathlib

theorem solution {a b : ℝ} : Dense (AddSubgroup.closure ({a, b} : Set ℝ) : Set ℝ) ↔ Irrational (a / b) :=
  dense_addSubgroupClosure_pair_iff
