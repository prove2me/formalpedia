-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_stronglyPredictable_inclusive_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T13:18:04.792407+00:00
-- url     : https://prove2.me/submissions/156621a8-8583-489b-82ca-adfcb784f240

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal

/-- Cutting a predictable integrand at a deterministic inclusive finite
horizon preserves the original-filtration strong predictability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Z : ℝ≥0 → Ω → ℝ)
    (hZ : IsStronglyPredictable 𝓕 Z)
    (T : ℝ≥0) :
    IsStronglyPredictable 𝓕
      (fun t ω => if t ≤ T then Z t ω else 0) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.predictable
  have hIoi : MeasurableSet
      (Set.Ioi T ×ˢ (Set.univ : Set Ω)) :=
    measurableSet_predictable_Ioi_prod (𝓕 := 𝓕) (i := T) MeasurableSet.univ
  have hIic : MeasurableSet
      (Set.Iic T ×ˢ (Set.univ : Set Ω)) := by
    have heq :
        (Set.Iic T ×ˢ (Set.univ : Set Ω)) =
          (Set.univ : Set (ℝ≥0 × Ω)) \
            (Set.Ioi T ×ˢ (Set.univ : Set Ω)) := by
      ext ⟨t, ω⟩
      simp [Set.mem_prod, not_lt]
    rw [heq]
    exact MeasurableSet.univ.diff hIoi
  have htime : MeasurableSet {p : ℝ≥0 × Ω | p.1 ≤ T} := by
    have heq : {p : ℝ≥0 × Ω | p.1 ≤ T} =
        Set.Iic T ×ˢ (Set.univ : Set Ω) := by
      ext ⟨t, ω⟩
      simp [Set.mem_prod]
    rw [heq]
    exact hIic
  change StronglyMeasurable (fun p : ℝ≥0 × Ω =>
    if p.1 ≤ T then Z p.1 p.2 else 0)
  exact ((hZ.measurable).ite htime measurable_const).stronglyMeasurable
