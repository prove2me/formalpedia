-- Prove2me | solution 1 for AvramDividend.Classical.levy_lowerCrossing_before_filtration_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T07:31:03.221767+00:00
-- url     : https://prove2.me/submissions/7b8b8b0d-419a-4f08-93ae-d07cec038978

import Mathlib.Probability.Process.Adapted
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_lower_before_horizon_countable_grid_iff

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Ruin below a fixed threshold before T is observable by T. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (lower : ℝ) (T : ℝ≥0) :
    MeasurableSet[𝓕 T]
      {ω : Ω | ∃ s : ℝ≥0, s < T ∧ X.X s ω < lower} := by
  have hGrid : ∀ n k : ℕ, MeasurableSet[𝓕 T]
      {ω : Ω | (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < T ∧
        X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω < lower} := by
    intro n k
    by_cases hT : (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < T
    · have hZ : Measurable[𝓕 T]
          (X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹)) :=
        (X.adapted _).mono (𝓕.mono hT.le) le_rfl
      simpa only [hT, true_and] using
        (measurableSet_lt hZ measurable_const)
    · letI : MeasurableSpace Ω := 𝓕 T
      simpa only [hT, false_and, setOf_false] using
        (MeasurableSet.empty : MeasurableSet (∅ : Set Ω))
  have hOuter : ∀ n : ℕ, MeasurableSet[𝓕 T]
      {ω : Ω | 0 < n ∧ ∃ k : ℕ,
        (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < T ∧
        X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω < lower} := by
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
        X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω < lower} := by
    simpa only [Set.iUnion_setOf] using (MeasurableSet.iUnion hOuter)
  have hEq :
      {ω : Ω | ∃ s : ℝ≥0, s < T ∧ X.X s ω < lower} =
      {ω : Ω | ∃ n : ℕ, 0 < n ∧ ∃ k : ℕ,
        (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < T ∧
        X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω < lower} := by
    ext ω
    exact chat03_lower_before_horizon_countable_grid_iff X ω lower T
  rw [hEq]
  exact hCount
