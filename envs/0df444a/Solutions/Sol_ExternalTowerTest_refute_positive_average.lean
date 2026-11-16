-- Prove2me | solution 1 for ExternalTowerTest.refute_positive_average
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-16T03:33:57.283205+00:00
-- url     : https://prove2.me/submissions/d05c3918-1f9b-44d7-a1a8-fd53b3e9ca53

import Mathlib
open Filter Topology

theorem solution :
    ¬ (∀ a b : ℝ, a+b=1 →
      0 ≤ (3/4:ℝ)*a+(1/4:ℝ)*b →
      0 ≤ (1/4:ℝ)*a+(3/4:ℝ)*b → 0 ≤ a ∧ 0 ≤ b) := by
  intro h
  have hb := (h (3/2) (-1/2) (by norm_num) (by norm_num) (by norm_num)).2
  norm_num at hb
