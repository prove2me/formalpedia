-- Prove2me | solution 2 for AvramDividend.Classical.shifted_lower_survival_filtration_measurable_no_schedule
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T21:53:58.705188+00:00
-- url     : https://prove2.me/submissions/bba3b8ba-3e95-444a-b3b7-ea725a7287bd

import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Theorems.Thm_AvramDividend_Classical_levy_lowerCrossing_before_filtration_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

/-- Continuous-time shifted survival is observable at the horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (T : ℝ≥0) :
    MeasurableSet[𝓕 T]
      {ω : Ω | ∀ s : ℝ≥0, s ≤ T → 0 ≤ x + X.X s ω} := by
  have hBefore : MeasurableSet[𝓕 T]
      {ω : Ω | ∃ s : ℝ≥0, s < T ∧ X.X s ω < -x} :=
    levy_lowerCrossing_before_filtration_measurable X (-x) T
  have hXT : Measurable[𝓕 T] (X.X T) :=
    (X.adapted T).mono (𝓕.mono le_rfl) le_rfl
  have hTerminal : MeasurableSet[𝓕 T] {ω : Ω | X.X T ω < -x} :=
    measurableSet_lt hXT measurable_const
  have hBad : MeasurableSet[𝓕 T]
      {ω : Ω | ∃ s : ℝ≥0, s ≤ T ∧ X.X s ω < -x} := by
    have hUnion :
        {ω : Ω | ∃ s : ℝ≥0, s ≤ T ∧ X.X s ω < -x} =
          {ω : Ω | ∃ s : ℝ≥0, s < T ∧ X.X s ω < -x} ∪
            {ω : Ω | X.X T ω < -x} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_union]
      constructor
      · rintro ⟨s, hs, hb⟩
        rcases lt_or_eq_of_le hs with hlt | heq
        · exact Or.inl ⟨s, hlt, hb⟩
        · subst s
          exact Or.inr hb
      · rintro (⟨s, hs, hb⟩ | hb)
        · exact ⟨s, hs.le, hb⟩
        · exact ⟨T, le_rfl, hb⟩
    rw [hUnion]
    letI : MeasurableSpace Ω := 𝓕 T
    exact hBefore.union hTerminal
  have hGood :
      {ω : Ω | ∀ s : ℝ≥0, s ≤ T → 0 ≤ x + X.X s ω} =
        {ω : Ω | ∃ s : ℝ≥0, s ≤ T ∧ X.X s ω < -x}ᶜ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
    constructor
    · intro hSurv ⟨s, hs, hb⟩
      have hNonneg := hSurv s hs
      linarith
    · intro hAvoid s hs
      by_contra hNeg
      have hb : X.X s ω < -x := by linarith
      exact hAvoid ⟨s, hs, hb⟩
  rw [hGood]
  letI : MeasurableSpace Ω := 𝓕 T
  exact hBad.compl
