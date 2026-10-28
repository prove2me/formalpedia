-- Prove2me | solution 1 for AvramDividend.Classical.chat04_actual_exponential_clock_joint_terminal_reversal_ws01a
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T12:55:02.357187+00:00
-- url     : https://prove2.me/submissions/509564eb-827c-479f-aeef-da390d0e5b59

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat04_terminal_restricted_fixed_horizon_strict_reversal_ws01a
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_joint_weighted_clock_section_probability_transfer
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_levy_random_horizon_strict_events_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (r : ℝ) (hr : 0 < r) (a c : ℝ) :
    ((P.prod (expMeasure r)).withDensity
      (fun z : Ω × ℝ =>
        if X.X z.2.toNNReal z.1 - X.X 0 z.1 < c
        then (1 : ℝ≥0∞) else 0))
      {z : Ω × ℝ | ∃ s : ℝ≥0, s ≤ z.2.toNNReal ∧
        X.X z.2.toNNReal z.1 - X.X s z.1 < a} =
    ((P.prod (expMeasure r)).withDensity
      (fun z : Ω × ℝ =>
        if X.X z.2.toNNReal z.1 - X.X 0 z.1 < c
        then (1 : ℝ≥0∞) else 0))
      {z : Ω × ℝ | ∃ s : ℝ≥0, s ≤ z.2.toNNReal ∧
        X.X s z.1 - X.X 0 z.1 < a} := by
  letI : IsProbabilityMeasure P := X.isProbability
  letI : IsProbabilityMeasure (expMeasure r) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hr
  let D : Ω × ℝ → ℝ≥0∞ := fun z =>
    if X.X z.2.toNNReal z.1 - X.X 0 z.1 < c then 1 else 0
  have hXT : Measurable (fun z : Ω × ℝ =>
      X.X z.2.toNNReal z.1) :=
    (chat04_levy_joint_time_state_measurable X).comp
      ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst)
  have hX0 : Measurable (fun z : Ω × ℝ => X.X 0 z.1) :=
    (X.adapted.measurable).comp measurable_fst
  have hD : Measurable D := by
    classical
    change Measurable (fun z : Ω × ℝ =>
      if z ∈ (fun y : Ω × ℝ =>
        X.X y.2.toNNReal y.1 - X.X 0 y.1) ⁻¹' Iio c
      then (1 : ℝ≥0∞) else 0)
    exact Measurable.ite
      (measurableSet_Iio.preimage (hXT.sub hX0))
      measurable_const measurable_const
  obtain ⟨hL, hR⟩ :=
    avram_ws01e_b_levy_random_horizon_strict_events_measurable
      X (fun t : ℝ => t.toNNReal) measurable_real_toNNReal a
  refine avram_ws01e_b_joint_weighted_clock_section_probability_transfer
    P (expMeasure r) D hD _ _ hL hR ?_
  intro t
  by_cases ht : 0 < t.toNNReal
  · exact chat04_terminal_restricted_fixed_horizon_strict_reversal_ws01a
      X t.toNNReal ht a c
  · have hz : t.toNNReal = 0 :=
      le_antisymm (le_of_not_gt ht) zero_le
    have hLeft :
        {ω : Ω | ∃ s : ℝ≥0, s ≤ t.toNNReal ∧
          X.X t.toNNReal ω - X.X s ω < a} =
        {ω : Ω | 0 < a} := by
      ext ω
      constructor
      · rintro ⟨s, hs, h⟩
        have hs0 : s = 0 := le_antisymm (by simpa [hz] using hs) zero_le
        simpa [hz, hs0] using h
      · intro ha
        exact ⟨0, by simp [hz], by simpa [hz] using ha⟩
    have hRight :
        {ω : Ω | ∃ s : ℝ≥0, s ≤ t.toNNReal ∧
          X.X s ω - X.X 0 ω < a} =
        {ω : Ω | 0 < a} := by
      ext ω
      constructor
      · rintro ⟨s, hs, h⟩
        have hs0 : s = 0 := le_antisymm (by simpa [hz] using hs) zero_le
        simpa [hs0] using h
      · intro ha
        exact ⟨0, by simp [hz], by simpa using ha⟩
    change
      (P.withDensity (fun ω : Ω => D (ω, t)))
        {ω : Ω | ∃ s : ℝ≥0, s ≤ t.toNNReal ∧
          X.X t.toNNReal ω - X.X s ω < a} =
      (P.withDensity (fun ω : Ω => D (ω, t)))
        {ω : Ω | ∃ s : ℝ≥0, s ≤ t.toNNReal ∧
          X.X s ω - X.X 0 ω < a}
    rw [hLeft, hRight]
