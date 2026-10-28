-- Prove2me | solution 1 for AvramDividend.Classical.affine_cutoff_deriv_eq_one_positive
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:17:14.954412+00:00
-- url     : https://prove2.me/submissions/ed4fd356-00a1-4572-a53d-51bab3519a6a

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

open Filter Set
open scoped Topology
theorem solution
    (y : ℝ) (hy : 0 < y) :
    deriv (fun z : ℝ => if z < 0 then 0 else z - 1) y = 1 := by
  have h : (fun z : ℝ => if z < 0 then 0 else z - 1) =ᶠ[𝓝 y] fun z => z - 1 := by
    filter_upwards [lt_mem_nhds hy] with z hz
    simp [not_lt.2 hz.le]
  rw [h.deriv_eq]
  exact HasDerivAt.deriv (by simpa using (hasDerivAt_id y).sub_const (1:ℝ))
