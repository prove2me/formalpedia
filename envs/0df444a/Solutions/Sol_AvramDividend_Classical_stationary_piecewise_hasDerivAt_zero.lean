-- Prove2me | solution 1 for AvramDividend.Classical.stationary_piecewise_hasDerivAt_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T08:03:45.922754+00:00
-- url     : https://prove2.me/submissions/ede770bc-c443-4c7a-9d69-c313f48d43e1

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Piecewise

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Topology

/-- Smooth pasting of a stationary left branch to a constant right branch. -/
theorem solution
    (f : ℝ → ℝ) (c v : ℝ)
    (hdiff : DifferentiableAt ℝ f c)
    (hflat : deriv f c = 0)
    (hmatch : f c = v) :
    HasDerivAt ((Iic c).piecewise f (fun _ : ℝ => v)) 0 c := by
  have hfzero : HasDerivAt f 0 c := by
    rw [← hflat]
    exact hdiff.hasDerivAt
  have hleft : HasDerivWithinAt
      ((Iic c).piecewise f (fun _ : ℝ => v)) 0 (Iic c) c := by
    apply hfzero.hasDerivWithinAt.congr_of_mem
    · intro y hy
      simp [Set.piecewise, hy]
    · simp
  have hright : HasDerivWithinAt
      ((Iic c).piecewise f (fun _ : ℝ => v)) 0 (Ici c) c := by
    apply (hasDerivAt_const c v).hasDerivWithinAt.congr_of_mem
    · intro y hy
      by_cases hcy : y ≤ c
      · have hyeq : y = c := le_antisymm hcy hy
        subst y
        simpa [Set.piecewise] using hmatch
      · simp [Set.piecewise, hcy]
    · simp
  have hjoin := hleft.union hright
  have hcover : Iic c ∪ Ici c = (Set.univ : Set ℝ) := by
    ext y
    simp only [mem_union, mem_Iic, mem_Ici, mem_univ, iff_true]
    exact le_total y c
  rw [hcover] at hjoin
  exact hjoin.hasDerivAt (by simp)
