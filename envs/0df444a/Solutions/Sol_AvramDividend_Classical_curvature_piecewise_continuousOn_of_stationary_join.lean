-- Prove2me | solution 1 for AvramDividend.Classical.curvature_piecewise_continuousOn_of_stationary_join
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T07:59:33.754561+00:00
-- url     : https://prove2.me/submissions/a865fe5f-05ee-4ef8-a534-b79fff96292d

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Piecewise
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Data.Set.Operations

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Topology

/-- Continuous pasting of Gaussian curvature to the affine region. -/
theorem solution
    (W : ℝ → ℝ) (c : ℝ)
    (hcont : ContinuousOn (deriv (deriv W)) (Ioi (0 : ℝ)))
    (hflat : deriv (deriv W) c = 0) :
    ContinuousOn ((Iic c).piecewise (deriv (deriv W))
      (fun _ : ℝ => (0 : ℝ))) (Ioi (0 : ℝ)) := by
  have hright : ContinuousOn (fun _ : ℝ => (0 : ℝ))
      (Ioi (0 : ℝ)) := continuousOn_const
  have hboundary : EqOn (deriv (deriv W))
      (fun _ : ℝ => (0 : ℝ))
      (Ioi (0 : ℝ) ∩ frontier (Iic c)) := by
    intro y hy
    have hyc : y = c := by
      simpa [frontier_Iic] using hy.2
    subst y
    exact hflat
  have hp := continuousOn_piecewise_ite hcont hright (by rfl) hboundary
  simpa using hp
