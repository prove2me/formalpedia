-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_02c_deterministic_horizon_mask_original_predictable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T14:24:20.76312+00:00
-- url     : https://prove2.me/submissions/76fc741b-6418-4ecb-a1fd-a69529c6b341

import Mathlib.Probability.Process.Predictable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0) :
    MeasurableSet[(@Prod.instMeasurableSpace _ _
      (𝓕.predictable) (inferInstance : MeasurableSpace ℝ))]
      {p : ((ℝ≥0 × Ω) × ℝ) | p.1.1 ≤ T} := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.predictable
  change MeasurableSet {p : ((ℝ≥0 × Ω) × ℝ) | p.1.1 ≤ T}
  have hIoi : MeasurableSet (Ioi T ×ˢ (Set.univ : Set Ω)) := by
    exact measurableSet_predictable_Ioi_prod (𝓕 := 𝓕)
      (MeasurableSet.univ : MeasurableSet[𝓕 T] (Set.univ : Set Ω))
  have hIic : MeasurableSet {p : ℝ≥0 × Ω | p.1 ≤ T} := by
    convert hIoi.compl using 1
    ext p
    simp
  have hProd : MeasurableSet
      ({p : ℝ≥0 × Ω | p.1 ≤ T} ×ˢ (Set.univ : Set ℝ)) :=
    hIic.prod MeasurableSet.univ
  convert hProd using 1
  ext p
  simp
