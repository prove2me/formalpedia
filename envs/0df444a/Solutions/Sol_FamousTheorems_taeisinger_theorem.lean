-- Prove2me | solution 1 for FamousTheorems.taeisinger_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:16:26.516266+00:00
-- url     : https://prove2.me/submissions/40f90227-24ef-46f9-81b7-770404b09644

import Mathlib

theorem solution {n : ℕ} (hn : 2 ≤ n) : ¬(harmonic n).isInt :=
  harmonic_not_int hn
