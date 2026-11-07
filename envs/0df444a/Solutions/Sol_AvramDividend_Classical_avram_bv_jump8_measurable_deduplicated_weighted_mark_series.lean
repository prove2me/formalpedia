-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_measurable_deduplicated_weighted_mark_series
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T00:36:54.101654+00:00
-- url     : https://prove2.me/submissions/e93d7fbe-2c9c-4bd4-b160-45c0ddf54c59

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Measurability of the deduplicated nonnegative marked jump series. -/
theorem solution
    (time : ℕ → (ℝ≥0 → ℝ) → ℝ≥0)
    (mark : ℕ → (ℝ≥0 → ℝ) → ℝ)
    (hTime : ∀ k, Measurable (time k))
    (hMark : ∀ k, Measurable (mark k))
    (T : ℝ≥0) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    Measurable (fun Y : ℝ≥0 → ℝ =>
      ∑' k : ℕ,
        if 0 < time k Y ∧ time k Y ≤ T ∧
            (∀ j : ℕ, j < k → time j Y ≠ time k Y)
        then g (mark k Y) else 0) := by
  apply Measurable.ennreal_tsum
  intro k
  have hUnique : MeasurableSet
      {Y : ℝ≥0 → ℝ | ∀ j : ℕ, j < k → time j Y ≠ time k Y} := by
    have hj : ∀ j : ℕ, MeasurableSet
        {Y : ℝ≥0 → ℝ | j < k → time j Y ≠ time k Y} := by
      intro j
      by_cases h : j < k
      · have hNeq : MeasurableSet
            {Y : ℝ≥0 → ℝ | time j Y ≠ time k Y} :=
          (measurableSet_eq_fun (hTime j) (hTime k)).compl
        have heq :
            {Y : ℝ≥0 → ℝ | j < k → time j Y ≠ time k Y} =
              {Y : ℝ≥0 → ℝ | time j Y ≠ time k Y} := by
          ext Y
          simp [h]
        rw [heq]
        exact hNeq
      · simp [h]
    convert MeasurableSet.iInter hj using 1
    ext Y
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
  have hWindow : MeasurableSet
      {Y : ℝ≥0 → ℝ | 0 < time k Y ∧ time k Y ≤ T ∧
        (∀ j : ℕ, j < k → time j Y ≠ time k Y)} := by
    exact (measurableSet_lt measurable_const (hTime k)).inter
      ((measurableSet_le (hTime k) measurable_const).inter hUnique)
  exact (hg.comp (hMark k)).ite hWindow measurable_const
