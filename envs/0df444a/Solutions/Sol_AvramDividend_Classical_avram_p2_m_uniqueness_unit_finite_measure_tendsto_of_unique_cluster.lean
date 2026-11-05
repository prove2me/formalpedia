-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_m_uniqueness_unit_finite_measure_tendsto_of_unique_cluster
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T12:18:28.200404+00:00
-- url     : https://prove2.me/submissions/48ecc1f4-8e3c-4ef0-a287-72bf1aa28ca5

import Mathlib.Topology.Compactness.Compact
import Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_unit_finite_measure_family_compact

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal

/-- Compactness plus identification of every weak cluster point gives
full filter convergence, without a first-countability assumption. -/
theorem solution
    {ι : Type*} (l : Filter ι)
    (C : ℝ≥0) (μi : ι → FiniteMeasure ℝ) (ρ : FiniteMeasure ℝ)
    (hmass : ∀ i, (μi i).mass ≤ C)
    (hunit : ∀ i, (μi i) (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (hunique : ∀ σ : FiniteMeasure ℝ,
      σ.mass ≤ C → σ (Set.Icc (0 : ℝ) 1)ᶜ = 0 →
        MapClusterPt σ l μi → σ = ρ) :
    Tendsto μi l (nhds ρ) := by
  let K : Set (FiniteMeasure ℝ) :=
    {μ | μ.mass ≤ C ∧ μ (Set.Icc (0 : ℝ) 1)ᶜ = 0}
  have hc : IsCompact K :=
    AvramDividend.Classical.avram_p2_m_uniqueness_unit_finite_measure_family_compact C
  have hm : ∀ᶠ i in l, μi i ∈ K :=
    Filter.Eventually.of_forall (fun i => ⟨hmass i, hunit i⟩)
  exact hc.tendsto_nhds_of_unique_mapClusterPt hm
    (fun σ hσ hcluster => hunique σ hσ.1 hσ.2 hcluster)
