-- Prove2me | solution 1 for AvramDividend.Classical.shifted_lower_survival_filtration_measurable_no_schedule
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T21:53:34.314992+00:00
-- url     : https://prove2.me/submissions/e87714e4-6fef-4235-a77b-dd9adc3d5743

import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Theorems.Thm_AvramDividend_Classical_levy_lowerCrossing_before_filtration_measurable

open MeasureTheory Set
open scoped NNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : AvramDividend.Classical.SpectrallyNegativeLevy P 𝓕) (x : ℝ) (T : ℝ≥0) :
    MeasurableSet[𝓕 T]
      {ω : Ω | ∀ s : ℝ≥0, s ≤ T → 0 ≤ x + X.X s ω} := by
  have h1 := (AvramDividend.Classical.levy_lowerCrossing_before_filtration_measurable X (-x) T).compl
  have h2 : MeasurableSet[𝓕 T] {ω : Ω | 0 ≤ x + X.X T ω} := by
    have hm : Measurable[𝓕 T] (fun ω => x + X.X T ω) :=
      measurable_const.add (X.adapted T)
    exact hm measurableSet_Ici
  convert h1.inter h2 using 1
  ext ω
  simp only [mem_setOf_eq, mem_inter_iff, mem_compl_iff, not_exists, not_and, not_lt]
  constructor
  · intro h
    exact ⟨fun s hs => by linarith [h s hs.le], h T le_rfl⟩
  · rintro ⟨h, hT⟩ s hs
    rcases hs.lt_or_eq with hs | rfl
    · linarith [h s hs]
    · exact hT
