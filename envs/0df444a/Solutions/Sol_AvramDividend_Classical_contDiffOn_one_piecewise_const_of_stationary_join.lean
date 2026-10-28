-- Prove2me | solution 1 for AvramDividend.Classical.contDiffOn_one_piecewise_const_of_stationary_join
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T08:12:25.623455+00:00
-- url     : https://prove2.me/submissions/622bb96c-7bf1-4201-b4fb-661f6be363cd

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.Piecewise
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Order.Interval.Set.LinearOrder
import Theorems.Thm_AvramDividend_Classical_stationary_piecewise_hasDerivAt_zero
import Theorems.Thm_AvramDividend_Classical_contDiffOn_one_Ioi_of_differentiableAt_continuous_deriv

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set Topology AvramDividend.Classical

/-- A stationary C1 profile pastes smoothly to a constant continuation. -/
theorem solution (f : ℝ → ℝ) (c v : ℝ) (hc : 0 < c)
    (hreg : ContDiffOn ℝ 1 f (Ioi (0 : ℝ)))
    (hflat : deriv f c = 0) (hmatch : f c = v) :
    ContDiffOn ℝ 1 ((Iic c).piecewise f (fun _ : ℝ => v))
      (Ioi (0 : ℝ)) := by
  let p : ℝ → ℝ := (Iic c).piecewise f (fun _ => v)
  have hfdiff (x : ℝ) (hx : 0 < x) : DifferentiableAt ℝ f x :=
    (hreg.differentiableOn_one x hx).differentiableAt
      (Ioi_mem_nhds hx)
  have hpjoin : HasDerivAt p 0 c := by
    simpa [p] using stationary_piecewise_hasDerivAt_zero
      f c v (hfdiff c hc) hflat hmatch
  have hpdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ p x := by
    intro x hx
    by_cases hxc : x < c
    · have hlocal : p =ᶠ[𝓝 x] f := by
        filter_upwards [eventually_lt_nhds hxc] with y hy
        simp [p, Set.piecewise, hy.le]
      exact ((hfdiff x hx).hasDerivAt.congr_of_eventuallyEq
        hlocal).differentiableAt
    · by_cases hcx : c < x
      · have hlocal : p =ᶠ[𝓝 x] (fun _ : ℝ => v) := by
          filter_upwards [eventually_gt_nhds hcx] with y hy
          simp [p, Set.piecewise, not_le.mpr hy]
        exact ((hasDerivAt_const x v).congr_of_eventuallyEq
          hlocal).differentiableAt
      · have heq : x = c :=
          le_antisymm (le_of_not_gt hcx) (le_of_not_gt hxc)
        subst x
        exact hpjoin.differentiableAt
  have hleft : ContinuousOn (deriv f) (Ioi (0 : ℝ)) :=
    hreg.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl
  have hright : ContinuousOn (fun _ : ℝ => (0 : ℝ))
      (Ioi (0 : ℝ)) := continuousOn_const
  have hbound : EqOn (deriv f) (fun _ : ℝ => (0 : ℝ))
      (Ioi (0 : ℝ) ∩ frontier (Iic c)) := by
    intro y hy
    have hyc : y = c := by simpa [frontier_Iic] using hy.2
    subst y
    exact hflat
  have hpderivCont : ContinuousOn
      ((Iic c).piecewise (deriv f) (fun _ : ℝ => (0 : ℝ)))
      (Ioi (0 : ℝ)) := by
    have hp := continuousOn_piecewise_ite hleft hright (by rfl) hbound
    simpa using hp
  have hpderiv : ∀ x : ℝ, 0 < x →
      deriv p x = (Iic c).piecewise (deriv f)
        (fun _ : ℝ => (0 : ℝ)) x := by
    intro x hx
    by_cases hxc : x < c
    · have hlocal : p =ᶠ[𝓝 x] f := by
        filter_upwards [eventually_lt_nhds hxc] with y hy
        simp [p, Set.piecewise, hy.le]
      simp [Set.piecewise, hxc.le, hlocal.deriv_eq]
    · by_cases hcx : c < x
      · have hlocal : p =ᶠ[𝓝 x] (fun _ : ℝ => v) := by
          filter_upwards [eventually_gt_nhds hcx] with y hy
          simp [p, Set.piecewise, not_le.mpr hy]
        simp [Set.piecewise, not_le.mpr hcx, hlocal.deriv_eq]
      · have heq : x = c :=
          le_antisymm (le_of_not_gt hcx) (le_of_not_gt hxc)
        subst x
        simp [Set.piecewise, hpjoin.deriv, hflat]
  have hpcont : ContinuousOn (deriv p) (Ioi (0 : ℝ)) := by
    apply hpderivCont.congr
    intro x hx
    exact hpderiv x hx
  simpa [p] using contDiffOn_one_Ioi_of_differentiableAt_continuous_deriv
    p hpdiff hpcont
