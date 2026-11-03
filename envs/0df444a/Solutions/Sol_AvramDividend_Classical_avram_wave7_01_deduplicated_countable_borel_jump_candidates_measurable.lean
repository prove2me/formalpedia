-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_deduplicated_countable_borel_jump_candidates_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:02:31.957472+00:00
-- url     : https://prove2.me/submissions/cbc96696-4740-4cac-a271-5260fde3fcc7

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

/-- A first-occurrence deduplicated Borel marked candidate jump count is measurable. -/
theorem solution
    {α : Type*} [mα : MeasurableSpace α]
    (time : ℕ → α → ℝ≥0) (mark : ℕ → α → ℝ)
    (htime : ∀ n : ℕ, Measurable (time n))
    (hmark : ∀ n : ℕ, Measurable (mark n))
    (T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
    Measurable (fun x : α =>
      ∑' n : ℕ,
        if 0 < time n x ∧ time n x ≤ T ∧ mark n x ∈ B ∧
          (∀ j : ℕ, j < n → time j x ≠ time n x)
        then (1 : ℝ≥0∞) else 0) := by
  apply Measurable.ennreal_tsum
  intro n
  have hPos : MeasurableSet {x : α | (0 : ℝ≥0) < time n x} := by
    simpa [Set.preimage] using
      ((measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ≥0))).preimage (htime n))
  have hBound : MeasurableSet {x : α | time n x ≤ T} := by
    simpa [Set.preimage] using
      ((measurableSet_Iic : MeasurableSet (Iic T)).preimage (htime n))
  have hMarked : MeasurableSet {x : α | mark n x ∈ B} := by
    simpa [Set.preimage] using hB.preimage (hmark n)
  have hDistinct (j : ℕ) :
      MeasurableSet {x : α | j < n → time j x ≠ time n x} := by
    have hDiff : MeasurableSet {x : α | time j x ≠ time n x} := by
      convert (measurableSet_eq_fun (htime j) (htime n)).compl using 1
      ext x
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, ne_eq]
    by_cases hj : j < n
    · simpa only [hj, true_implies] using hDiff
    · simp [hj]
  have hUnique :
      MeasurableSet {x : α | ∀ j : ℕ, j < n → time j x ≠ time n x} := by
    simpa only [Set.setOf_forall] using MeasurableSet.iInter hDistinct
  have hCell : MeasurableSet
      {x : α | 0 < time n x ∧ time n x ≤ T ∧ mark n x ∈ B ∧
        (∀ j : ℕ, j < n → time j x ≠ time n x)} := by
    convert hPos.inter (hBound.inter (hMarked.inter hUnique)) using 1
    ext x
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  exact measurable_const.ite hCell measurable_const
