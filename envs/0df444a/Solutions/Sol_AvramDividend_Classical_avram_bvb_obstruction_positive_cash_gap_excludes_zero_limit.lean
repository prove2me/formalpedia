-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_positive_cash_gap_excludes_zero_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T00:52:24.938426+00:00
-- url     : https://prove2.me/submissions/846175e3-f5a9-4d18-8d7b-94f438d19350

import Mathlib
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Separation.Hausdorff
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter
open scoped Topology
theorem solution (F L : ℕ → ℝ) (a b : ℝ) (hF : Tendsto F atTop (𝓝 a)) (hL : Tendsto L atTop (𝓝 (0 : ℝ))) (hgap : b < a) : ¬ Tendsto (fun n => max (F n - (b + L n)) 0) atTop (𝓝 (0 : ℝ)) := by
  intro hzero
  have hbase : Tendsto (fun n => F n - (b + L n)) atTop (𝓝 (a - (b + 0))) :=
    hF.sub (tendsto_const_nhds.add hL)
  have hmax : Tendsto (fun n => max (F n - (b + L n)) 0) atTop
      (𝓝 (max (a - (b + 0)) 0)) := hbase.max tendsto_const_nhds
  have heq : max (a - (b + 0)) 0 = (0 : ℝ) := tendsto_nhds_unique hmax hzero
  have hpos : 0 < a - (b + 0) := by linarith
  rw [max_eq_left (le_of_lt hpos)] at heq
  linarith
