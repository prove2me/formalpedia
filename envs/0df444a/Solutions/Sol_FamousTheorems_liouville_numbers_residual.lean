-- Prove2me | solution 1 for FamousTheorems.liouville_numbers_residual
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:20:21.032526+00:00
-- url     : https://prove2.me/submissions/f98a5caf-12ac-4c64-ade5-256abb0642f3

import Mathlib

theorem solution : ∀ᶠ x in residual ℝ, Liouville x :=
  eventually_residual_liouville
