-- Prove2me | solution 1 for ExternalTowerTest.all_upper_levels_negative
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-16T03:32:33.029931+00:00
-- url     : https://prove2.me/submissions/eab89f1d-a549-4955-89b1-e2ed5598ecae

import Mathlib
open Filter Topology

theorem solution (k : ℕ) (hk : 1 ≤ k) : ((1 - (2 : ℝ)^k)/2) < 0 := by
  have hp : (1 : ℝ) < 2^k := one_lt_pow₀ (by norm_num) (by omega)
  linarith
