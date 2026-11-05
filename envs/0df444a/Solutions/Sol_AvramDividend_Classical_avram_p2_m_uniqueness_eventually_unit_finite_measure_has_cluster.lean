-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_m_uniqueness_eventually_unit_finite_measure_has_cluster
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T12:27:13.208438+00:00
-- url     : https://prove2.me/submissions/9893f4df-6de6-4698-885b-1a3ca327ed55

import Mathlib.Topology.Compactness.Compact
import Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_unit_finite_measure_family_compact

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal

/-- Eventual compact support and mass bounds suffice for a weak cluster
point. This matches a small-time filter without redefining its family. -/
theorem solution
    {ι : Type*} (l : Filter ι) [NeBot l]
    (C : ℝ≥0) (μi : ι → FiniteMeasure ℝ)
    (hmass : ∀ᶠ i in l, (μi i).mass ≤ C)
    (hunit : ∀ᶠ i in l, (μi i) (Set.Icc (0 : ℝ) 1)ᶜ = 0) :
    ∃ μ : FiniteMeasure ℝ,
      μ.mass ≤ C ∧ μ (Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧
        MapClusterPt μ l μi := by
  let K : Set (FiniteMeasure ℝ) :=
    {μ | μ.mass ≤ C ∧ μ (Set.Icc (0 : ℝ) 1)ᶜ = 0}
  have hc : IsCompact K :=
    AvramDividend.Classical.avram_p2_m_uniqueness_unit_finite_measure_family_compact C
  have hmem : ∀ᶠ i in l, μi i ∈ K := hmass.and hunit
  obtain ⟨μ, hμ, hcluster⟩ := hc.exists_mapClusterPt_of_frequently hmem.frequently
  exact ⟨μ, hμ.1, hμ.2, hcluster⟩
