-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_m_uniqueness_eventually_unit_finite_measure_tendsto_of_unique_cluster
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T12:27:05.095551+00:00
-- url     : https://prove2.me/submissions/35137541-96d5-4cb8-bf67-c7910959f730

import Mathlib.Topology.Compactness.Compact
import Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_unit_finite_measure_family_compact

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal

/-- Eventual compact support plus uniqueness of cluster points yields
full weak convergence along the original filter. -/
theorem solution
    {ι : Type*} (l : Filter ι)
    (C : ℝ≥0) (μi : ι → FiniteMeasure ℝ) (ρ : FiniteMeasure ℝ)
    (hmass : ∀ᶠ i in l, (μi i).mass ≤ C)
    (hunit : ∀ᶠ i in l, (μi i) (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (hunique : ∀ σ : FiniteMeasure ℝ,
      σ.mass ≤ C → σ (Set.Icc (0 : ℝ) 1)ᶜ = 0 →
        MapClusterPt σ l μi → σ = ρ) :
    Tendsto μi l (nhds ρ) := by
  let K : Set (FiniteMeasure ℝ) :=
    {μ | μ.mass ≤ C ∧ μ (Set.Icc (0 : ℝ) 1)ᶜ = 0}
  have hc : IsCompact K :=
    AvramDividend.Classical.avram_p2_m_uniqueness_unit_finite_measure_family_compact C
  have hmem : ∀ᶠ i in l, μi i ∈ K := hmass.and hunit
  exact hc.tendsto_nhds_of_unique_mapClusterPt hmem
    (fun σ hσ hcluster => hunique σ hσ.1 hσ.2 hcluster)
