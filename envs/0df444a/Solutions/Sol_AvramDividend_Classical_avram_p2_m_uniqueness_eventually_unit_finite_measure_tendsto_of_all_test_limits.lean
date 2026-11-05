-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_m_uniqueness_eventually_unit_finite_measure_tendsto_of_all_test_limits
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T12:35:37.616237+00:00
-- url     : https://prove2.me/submissions/738db4d5-f22e-4602-8c54-be24cfa14db5

import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Prokhorov
import Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_eventually_unit_finite_measure_tendsto_of_unique_cluster
import Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_cluster_bounded_nonnegative_lintegral_eq

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology BoundedContinuousFunction
open scoped NNReal ENNReal

/-- All bounded continuous nonnegative test limits identify each cluster point;
compactness then yields weak convergence under eventual support and mass bounds. -/
theorem solution
    {ι : Type*} (l : Filter ι)
    (C : ℝ≥0) (μi : ι → FiniteMeasure ℝ) (ρ : FiniteMeasure ℝ)
    (hmass : ∀ᶠ i in l, (μi i).mass ≤ C)
    (hunit : ∀ᶠ i in l, (μi i) (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (hlim : ∀ f : ℝ →ᵇ ℝ≥0,
      Tendsto (fun i => ∫⁻ x, f x ∂μi i) l (nhds (∫⁻ x, f x ∂ρ))) :
    Tendsto μi l (nhds ρ) := by
  apply AvramDividend.Classical.avram_p2_m_uniqueness_eventually_unit_finite_measure_tendsto_of_unique_cluster
    l C μi ρ hmass hunit
  intro σ hσmass hσunit hcluster
  apply FiniteMeasure.ext_of_forall_lintegral_eq
  intro f
  exact AvramDividend.Classical.avram_p2_m_uniqueness_cluster_bounded_nonnegative_lintegral_eq
    l μi σ hcluster f _ (hlim f)
