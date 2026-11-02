-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_02c_deterministic_horizon_mask_rightcont_predictable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T14:14:10.911527+00:00
-- url     : https://prove2.me/submissions/deef986e-dacc-4ea0-9019-089b458514d3

import Mathlib
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
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))]
      {p : ((ℝ≥0 × Ω) × ℝ) | p.1.1 ≤ T} := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  change MeasurableSet {p : ((ℝ≥0 × Ω) × ℝ) | p.1.1 ≤ T}
  have hIoi : MeasurableSet (Ioi T ×ˢ (Set.univ : Set Ω)) := by
    exact measurableSet_predictable_Ioi_prod (𝓕 := 𝓕.rightCont)
      (MeasurableSet.univ : MeasurableSet[𝓕.rightCont T] (Set.univ : Set Ω))
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
