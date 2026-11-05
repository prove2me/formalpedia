-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_m_uniqueness_unit_finite_measure_has_cluster
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T12:18:31.814541+00:00
-- url     : https://prove2.me/submissions/1c55f947-a967-47cf-b2d4-e0b8304f4be6

import Mathlib.MeasureTheory.Measure.Prokhorov
import Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_unit_finite_measure_family_compact

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal

/-- Every filter of compactly supported, uniformly mass-bounded finite
measures has a weak cluster point with the same bounds. No sequentiality
or first-countability assumption on the finite-measure space is needed. -/
theorem solution
    {ι : Type*} (l : Filter ι) [NeBot l]
    (C : ℝ≥0) (μi : ι → FiniteMeasure ℝ)
    (hmass : ∀ i, (μi i).mass ≤ C)
    (hunit : ∀ i, (μi i) (Set.Icc (0 : ℝ) 1)ᶜ = 0) :
    ∃ μ : FiniteMeasure ℝ,
      μ.mass ≤ C ∧ μ (Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧
        MapClusterPt μ l μi := by
  let K : Set (FiniteMeasure ℝ) :=
    {μ | μ.mass ≤ C ∧ μ (Set.Icc (0 : ℝ) 1)ᶜ = 0}
  have hc : IsCompact K :=
    AvramDividend.Classical.avram_p2_m_uniqueness_unit_finite_measure_family_compact C
  have hm : ∀ᶠ i in l, μi i ∈ K := by
    exact Filter.Eventually.of_forall (fun i => ⟨hmass i, hunit i⟩)
  obtain ⟨μ, hμ, hcluster⟩ := hc.exists_mapClusterPt_of_frequently hm.frequently
  exact ⟨μ, hμ.1, hμ.2, hcluster⟩
