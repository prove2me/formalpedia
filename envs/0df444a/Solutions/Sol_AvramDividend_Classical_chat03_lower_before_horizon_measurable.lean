-- Prove2me | solution 1 for AvramDividend.Classical.chat03_lower_before_horizon_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T06:41:28.636857+00:00
-- url     : https://prove2.me/submissions/d539deb6-d073-40f5-a53c-5c09115149dd

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_lower_before_horizon_countable_grid_iff
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

/-!
The occurrence of a strict lower passage before each deterministic
finite nonnegative horizon is measurable in the ambient sigma algebra.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower : ℝ) (T : ℝ≥0) :
    MeasurableSet {ω : Ω | ∃ s : ℝ≥0,
      s < T ∧ X.X s ω < lower} := by
  have hGrid : ∀ n k : ℕ, MeasurableSet
      {ω : Ω | (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < T ∧
        X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω < lower} := by
    intro n k
    have hZ : Measurable (X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹)) :=
      (X.adapted _).mono (𝓕.le _) le_rfl
    by_cases hT : (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < T
    · simpa only [hT, true_and] using
        (measurableSet_lt hZ measurable_const)
    · simpa only [hT, false_and, setOf_false] using
        (MeasurableSet.empty : MeasurableSet (∅ : Set Ω))
  have hOuter : ∀ n : ℕ, MeasurableSet
      {ω : Ω | 0 < n ∧ ∃ k : ℕ,
        (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < T ∧
        X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω < lower} := by
    intro n
    by_cases hn : 0 < n
    · simpa only [hn, true_and, Set.iUnion_setOf] using
        (MeasurableSet.iUnion (fun k : ℕ => hGrid n k))
    · simpa only [hn, false_and, setOf_false] using
        (MeasurableSet.empty : MeasurableSet (∅ : Set Ω))
  have hCount : MeasurableSet
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
