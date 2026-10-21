-- Prove2me | solution 1 for AvramDividend.Classical.chat03_upper_before_horizon_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T06:29:16.873824+00:00
-- url     : https://prove2.me/submissions/c943339f-2c57-46d9-870f-6789ab2bdadb

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_upper_before_horizon_countable_grid_iff
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

/-!
The upper strict-crossing occurrence event before any fixed finite
horizon is measurable, from countable strict grid observations.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (upper : ℝ) (T : ℝ≥0) :
    MeasurableSet {ω : Ω | ∃ s : ℝ≥0,
      s < T ∧ upper < X.X s ω} := by
  have hGrid : ∀ n k : ℕ, MeasurableSet
      {ω : Ω | (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < T ∧
        upper < X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω} := by
    intro n k
    have hZ : Measurable (X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹)) :=
      (X.adapted _).mono (𝓕.le _) le_rfl
    by_cases hT : (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < T
    · simpa only [hT, true_and] using
        (measurableSet_lt measurable_const hZ)
    · simpa only [hT, false_and, setOf_false] using
        (MeasurableSet.empty : MeasurableSet (∅ : Set Ω))
  have hOuter : ∀ n : ℕ, MeasurableSet
      {ω : Ω | 0 < n ∧ ∃ k : ℕ,
        (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < T ∧
        upper < X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω} := by
    intro n
    by_cases hn : 0 < n
    · simpa only [hn, true_and, Set.iUnion_setOf] using
        (MeasurableSet.iUnion (fun k : ℕ => hGrid n k))
    · simpa only [hn, false_and, setOf_false] using
        (MeasurableSet.empty : MeasurableSet (∅ : Set Ω))
  have hCount : MeasurableSet
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
  rw [hEq]
  exact hCount
