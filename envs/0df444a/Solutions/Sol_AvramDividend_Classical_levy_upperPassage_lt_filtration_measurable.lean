-- Prove2me | solution 1 for AvramDividend.Classical.levy_upperPassage_lt_filtration_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T07:40:48.254839+00:00
-- url     : https://prove2.me/submissions/0d512e1d-150a-48c9-943c-26ecaba100d8

import Mathlib.Probability.Process.Adapted
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_lt_iff_exists_witness
import Theorems.Thm_AvramDividend_Classical_chat03_upper_before_horizon_countable_grid_iff
import Theorems.Thm_AvramDividend_Classical_chat08_levy_upcrossing_event_measurable_at_time

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The strict upper first-passage clock is observable by each finite horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (upper : ℝ) (T : ℝ≥0) :
    MeasurableSet[𝓕 T]
      {ω : Ω |
        (⨅ (t : ℝ≥0) (_ : upper < X.X t ω), (t : ℝ≥0∞)) <
          (T : ℝ≥0∞)} := by
  have hGrid : ∀ n k : ℕ, MeasurableSet[𝓕 T]
      {ω : Ω | (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < T ∧
        upper < X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω} := by
    intro n k
    by_cases hT : (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < T
    · have hZ : Measurable[𝓕 T]
          (X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹)) :=
        (X.adapted _).mono (𝓕.mono hT.le) le_rfl
      simpa only [hT, true_and] using
        (measurableSet_lt measurable_const hZ)
    · letI : MeasurableSpace Ω := 𝓕 T
      simpa only [hT, false_and, setOf_false] using
        (MeasurableSet.empty : MeasurableSet (∅ : Set Ω))
  have hOuter : ∀ n : ℕ, MeasurableSet[𝓕 T]
      {ω : Ω | 0 < n ∧ ∃ k : ℕ,
        (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < T ∧
        upper < X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω} := by
    intro n
    by_cases hn : 0 < n
    · simpa only [hn, true_and, Set.iUnion_setOf] using
        (MeasurableSet.iUnion (fun k : ℕ => hGrid n k))
    · letI : MeasurableSpace Ω := 𝓕 T
      simpa only [hn, false_and, setOf_false] using
        (MeasurableSet.empty : MeasurableSet (∅ : Set Ω))
  have hCount : MeasurableSet[𝓕 T]
      {ω : Ω | ∃ n : ℕ, 0 < n ∧ ∃ k : ℕ,
        (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < T ∧
        upper < X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω} := by
    simpa only [Set.iUnion_setOf] using (MeasurableSet.iUnion hOuter)
  have hEq :
      {ω : Ω | ∃ s : ℝ≥0, s < T ∧ upper < X.X s ω} =
      {ω : Ω | ∃ n : ℕ, 0 < n ∧ ∃ k : ℕ,
        (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < T ∧
        upper < X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω} := by
    ext ω
    exact chat03_upper_before_horizon_countable_grid_iff X ω upper T
  have hPassage :
      {ω : Ω |
        (⨅ (t : ℝ≥0) (_ : upper < X.X t ω), (t : ℝ≥0∞)) <
          (T : ℝ≥0∞)} =
      {ω : Ω | ∃ s : ℝ≥0, s < T ∧ upper < X.X s ω} := by
    ext ω
    constructor
    · intro h
      rcases (firstUpcrossing_lt_iff_exists_witness X upper ω T).mp h with
        ⟨s, hs, ht⟩
      exact ⟨s, ht, hs⟩
    · rintro ⟨s, ht, hs⟩
      exact (firstUpcrossing_lt_iff_exists_witness X upper ω T).mpr
        ⟨s, hs, ht⟩
  rw [hPassage, hEq]
  exact hCount
