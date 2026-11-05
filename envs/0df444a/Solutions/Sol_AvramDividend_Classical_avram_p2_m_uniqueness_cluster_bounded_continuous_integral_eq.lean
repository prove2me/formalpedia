-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_m_uniqueness_cluster_bounded_continuous_integral_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T12:21:04.988392+00:00
-- url     : https://prove2.me/submissions/7f95af87-f98f-49e8-b498-dd27eb96a226

import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.Topology.ClusterPt
import Mathlib.Topology.Separation.Hausdorff

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology BoundedContinuousFunction

/-- A weak cluster point inherits each independently convergent bounded
continuous test integral. No sequential compactness is used. -/
theorem solution
    {ι : Type*} (l : Filter ι)
    (μi : ι → FiniteMeasure ℝ) (μ : FiniteMeasure ℝ)
    (hcluster : MapClusterPt μ l μi)
    (f : ℝ →ᵇ ℝ) (a : ℝ)
    (hlim : Tendsto (fun i => ∫ x, f x ∂μi i) l (nhds a)) :
    (∫ x, f x ∂μ) = a := by
  have hcont : Continuous (fun σ : FiniteMeasure ℝ => ∫ x, f x ∂σ) :=
    FiniteMeasure.continuous_integral_boundedContinuousFunction f
  have hc : MapClusterPt (∫ x, f x ∂μ) l
      (fun i => ∫ x, f x ∂μi i) :=
    hcluster.continuousAt_comp hcont.continuousAt
  exact eq_of_nhds_neBot (hc.clusterPt.mono hlim)
