-- Prove2me | solution 1 for AvramDividend.Classical.causal_l1_primitive_deriv_eq_continuous_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:48:08.525461+00:00
-- url     : https://prove2.me/submissions/1ab15d4b-cc30-4e44-bd70-4de5d71f3fe0

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped Topology

theorem solution
    (g : ℝ → ℝ)
    (hgInt : IntegrableOn g (Ioi (0 : ℝ)) volume)
    (hgCont : ContinuousOn g (Ioi (0 : ℝ))) :
    ∀ x : ℝ, 0 < x →
      deriv (fun y : ℝ => ∫ s in Ioc (0 : ℝ) y, g s ∂volume) x = g x := by
  intro x hx
  let G : ℝ → ℝ := fun y => ∫ s in Ioc (0 : ℝ) y, g s ∂volume
  have hAt : ContinuousAt g x := hgCont.continuousAt (Ioi_mem_nhds hx)
  have hMeas : StronglyMeasurableAtFilter g (𝓝 x) volume :=
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hgCont) x hx
  have hInt : IntervalIntegrable g volume (0 : ℝ) x := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hx.le).2
    exact hgInt.mono_set (by intro y hy; exact hy.1)
  have hFTC : HasDerivAt (fun y : ℝ => ∫ s in (0 : ℝ)..y, g s)
      (g x) x :=
    intervalIntegral.integral_hasDerivAt_right hInt hMeas hAt
  have hDeriv : HasDerivAt G (g x) x := by
    apply hFTC.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact (intervalIntegral.integral_of_le hy.le).symm
  exact hDeriv.deriv
