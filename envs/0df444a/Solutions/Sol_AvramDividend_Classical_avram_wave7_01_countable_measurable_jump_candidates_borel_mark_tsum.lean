-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_countable_measurable_jump_candidates_borel_mark_tsum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:02:34.702967+00:00
-- url     : https://prove2.me/submissions/b2c95085-4aca-41d8-ab3a-dd5a4cba1b7a

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

/-- Borel selection and counting of countably many jointly measurable candidate jump time-mark pairs. -/
theorem solution
    {α : Type*} [mα : MeasurableSpace α]
    (time : ℕ → α → ℝ≥0) (mark : ℕ → α → ℝ)
    (htime : ∀ n : ℕ, Measurable (time n))
    (hmark : ∀ n : ℕ, Measurable (mark n))
    (T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
    Measurable (fun x : α =>
      ∑' n : ℕ,
        if 0 < time n x ∧ time n x ≤ T ∧ mark n x ∈ B
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
  have hCell : MeasurableSet
      {x : α | 0 < time n x ∧ time n x ≤ T ∧ mark n x ∈ B} := by
    convert hPos.inter (hBound.inter hMarked) using 1
    ext x
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  exact measurable_const.ite hCell measurable_const
