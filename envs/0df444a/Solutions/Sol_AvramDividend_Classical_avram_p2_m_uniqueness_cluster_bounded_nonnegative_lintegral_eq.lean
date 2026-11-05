-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_m_uniqueness_cluster_bounded_nonnegative_lintegral_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T12:27:08.203735+00:00
-- url     : https://prove2.me/submissions/4de58e74-26aa-493c-b0a9-f8cee6650818

import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.Topology.ClusterPt
import Mathlib.Topology.Separation.Hausdorff

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped ENNReal NNReal

/-- A weak cluster point inherits the limit of each bounded continuous
nonnegative test lintegral, in the ENNReal topology. -/
theorem solution
    {ι : Type*} (l : Filter ι)
    (μi : ι → FiniteMeasure ℝ) (μ : FiniteMeasure ℝ)
    (hcluster : MapClusterPt μ l μi)
    (f : ℝ →ᵇ ℝ≥0) (a : ℝ≥0∞)
    (hlim : Tendsto (fun i => ∫⁻ x, f x ∂μi i) l (nhds a)) :
    (∫⁻ x, f x ∂μ) = a := by
  have hcont : Continuous (fun σ : FiniteMeasure ℝ => ∫⁻ x, f x ∂σ) :=
    FiniteMeasure.continuous_lintegral_boundedContinuousFunction f
  have hc : MapClusterPt (∫⁻ x, f x ∂μ) l
      (fun i => ∫⁻ x, f x ∂μi i) :=
    hcluster.continuousAt_comp hcont.continuousAt
  exact eq_of_nhds_neBot (hc.clusterPt.mono hlim)
