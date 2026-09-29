-- Prove2me | solution 1 for Erdos183.one_le_log_nat_of_three_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-04T00:28:40.365284+00:00
-- url     : https://prove2.me/submissions/25b28e57-dea4-4e3b-ba34-7e70b1d50905

import Definitions.Def_erdos183_core
import Mathlib.Analysis.Complex.ExponentialBounds

open Filter Finset SimpleGraph
open scoped Topology

open Erdos183

theorem solution (H : ℕ) (hH : 3 ≤ H) :
    1 ≤ Real.log (H : ℝ) := by
  have hpos : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
  apply (Real.le_log_iff_exp_le hpos).mpr
  calc
    Real.exp 1 ≤ (3 : ℝ) := Real.exp_one_lt_three.le
    _ ≤ (H : ℝ) := by exact_mod_cast hH
