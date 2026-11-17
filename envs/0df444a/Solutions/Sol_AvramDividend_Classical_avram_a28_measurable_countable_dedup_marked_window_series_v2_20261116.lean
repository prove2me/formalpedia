-- Prove2me | solution 1 for AvramDividend.Classical.avram_a28_measurable_countable_dedup_marked_window_series_v2_20261116
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T17:51:24.213227+00:00
-- url     : https://prove2.me/submissions/74d528ef-0ec9-4726-a3fb-71b26d7517c1

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
theorem solution
    (s T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (time : ℕ → (ℝ≥0 → ℝ) → ℝ≥0)
    (htime : ∀ k, Measurable (time k))
    (mark : ℕ → (ℝ≥0 → ℝ) → ℝ)
    (hmark : ∀ k, Measurable (mark k)) :
    Measurable (fun Y : ℝ≥0 → ℝ =>
      ∑' k : ℕ,
        if s < time k Y ∧ time k Y ≤ T ∧ mark k Y ∈ B ∧
            (∀ j : ℕ, j < k → time j Y ≠ time k Y)
        then (1 : ℝ≥0∞) else 0) := by
  classical
  apply Measurable.tsum
  intro k
  have hDistinct : MeasurableSet
      {Y : ℝ≥0 → ℝ | ∀ j : ℕ, j < k → time j Y ≠ time k Y} := by
    have hEach : ∀ j : ℕ, MeasurableSet
        {Y : ℝ≥0 → ℝ | j < k → time j Y ≠ time k Y} := by
      intro j
      by_cases hj : j < k
      · have hSet : {Y : ℝ≥0 → ℝ | j < k → time j Y ≠ time k Y} =
            {Y : ℝ≥0 → ℝ | time j Y ≠ time k Y} := by
          ext Y
          simp [hj]
        rw [hSet]
        exact (measurableSet_eq_fun (htime j) (htime k)).compl
      · have hSet : {Y : ℝ≥0 → ℝ | j < k → time j Y ≠ time k Y} =
            Set.univ := by
          ext Y
          simp [hj]
        rw [hSet]
        exact MeasurableSet.univ
    have hInter : MeasurableSet
        (⋂ j : ℕ, {Y : ℝ≥0 → ℝ | j < k → time j Y ≠ time k Y}) :=
      MeasurableSet.iInter hEach
    have hEq :
        {Y : ℝ≥0 → ℝ | ∀ j : ℕ, j < k → time j Y ≠ time k Y} =
        ⋂ j : ℕ, {Y : ℝ≥0 → ℝ | j < k → time j Y ≠ time k Y} := by
      ext Y
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [hEq]
    exact hInter
  have hCond : MeasurableSet
      {Y : ℝ≥0 → ℝ |
        s < time k Y ∧ time k Y ≤ T ∧ mark k Y ∈ B ∧
          (∀ j : ℕ, j < k → time j Y ≠ time k Y)} := by
    have hCond' : MeasurableSet
        (({Y : ℝ≥0 → ℝ | s < time k Y} ∩
            {Y : ℝ≥0 → ℝ | time k Y ≤ T}) ∩
          ({Y : ℝ≥0 → ℝ | mark k Y ∈ B} ∩
            {Y : ℝ≥0 → ℝ | ∀ j : ℕ,
              j < k → time j Y ≠ time k Y})) :=
      (((measurableSet_lt measurable_const (htime k)).inter
        (measurableSet_le (htime k) measurable_const)).inter
        ((hmark k hB).inter hDistinct))
    convert hCond' using 1
    ext Y
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    tauto
  exact measurable_const.ite hCond measurable_const
