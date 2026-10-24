-- Prove2me | solution 1 for AvramDividend.Classical.causal_primitive_deriv_eq_continuous_on_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:23:38.026587+00:00
-- url     : https://prove2.me/submissions/aa47edd5-ecd5-4b47-8f60-3d7f74dc016f

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped Topology

theorem solution
    (g : ℝ → ℝ) (hg : ContinuousOn g (Ici (0 : ℝ))) :
    ∀ x : ℝ, 0 < x →
      deriv (fun y : ℝ => ∫ s in Ioc (0 : ℝ) y, g s ∂volume) x = g x := by
  intro x hx
  let G : ℝ → ℝ := fun y => ∫ s in Ioc (0 : ℝ) y, g s ∂volume
  have hx' : x ∈ Ioi (0 : ℝ) := hx
  have hnhds : Ici (0 : ℝ) ∈ 𝓝 x :=
    Filter.mem_of_superset (Ioi_mem_nhds hx) Set.Ioi_subset_Ici_self
  have hAt : ContinuousAt g x := hg.continuousAt hnhds
  have hMeas : StronglyMeasurableAtFilter g (𝓝 x) volume :=
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi
      (hg.mono Set.Ioi_subset_Ici_self)) x hx'
  have hInt : IntervalIntegrable g volume (0 : ℝ) x := by
    apply ContinuousOn.intervalIntegrable
    apply hg.mono
    intro y hy
    have hxy : y ∈ Icc (0 : ℝ) x := by
      simpa [Set.uIcc_of_le hx.le] using hy
    exact hxy.1
  have hFTC : HasDerivAt (fun y : ℝ => ∫ s in (0 : ℝ)..y, g s) (g x) x :=
    intervalIntegral.integral_hasDerivAt_right hInt hMeas hAt
  have hDeriv : HasDerivAt G (g x) x := by
    apply hFTC.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact (intervalIntegral.integral_of_le hy.le).symm
  exact hDeriv.deriv
