-- Prove2me | solution 1 for FamousTheorems.real_least_upper_bound_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:17:57.345426+00:00
-- url     : https://prove2.me/submissions/e1848a4b-02c1-48bb-939a-292893b5e6dc

import Mathlib

theorem solution {s : Set ℝ} (hne : s.Nonempty) (hbdd : BddAbove s) : ∃ x : ℝ, IsLUB s x :=
  Real.exists_isLUB hne hbdd
