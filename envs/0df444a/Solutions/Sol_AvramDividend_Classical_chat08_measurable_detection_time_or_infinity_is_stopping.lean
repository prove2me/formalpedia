-- Prove2me | solution 1 for AvramDividend.Classical.chat08_measurable_detection_time_or_infinity_is_stopping
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:07:56.03299+00:00
-- url     : https://prove2.me/submissions/888dfd6e-25f4-4473-be5d-f889034e6394

import Mathlib.Probability.Process.Stopping

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

/-! A detection made at a deterministic time is a stopping time even with infinite default. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (ℱ : Filtration ℝ≥0 mΩ) (s : ℝ≥0)
    (A : Set Ω) (hA : MeasurableSet[ℱ s] A) :
    IsStoppingTime ℱ
      (fun ω => if ω ∈ A then (s : WithTop ℝ≥0) else ⊤) := by
  intro r
  have htop : ¬ (⊤ : WithTop ℝ≥0) ≤ (r : WithTop ℝ≥0) :=
    WithTop.not_top_le_coe r
  by_cases hsr : s ≤ r
  · have hs : (s : WithTop ℝ≥0) ≤ (r : WithTop ℝ≥0) := by
      exact_mod_cast hsr
    have heq :
        {ω | (if ω ∈ A then (s : WithTop ℝ≥0) else ⊤) ≤
          (r : WithTop ℝ≥0)} = A := by
      ext ω
      by_cases hω : ω ∈ A
      · simpa [hω] using hs
      · simpa [hω] using htop
    rw [heq]
    exact (ℱ.mono hsr) A hA
  · have hs : ¬ (s : WithTop ℝ≥0) ≤ (r : WithTop ℝ≥0) := by
      intro h
      exact hsr (by exact_mod_cast h)
    have heq :
        {ω | (if ω ∈ A then (s : WithTop ℝ≥0) else ⊤) ≤
          (r : WithTop ℝ≥0)} = ∅ := by
      ext ω
      by_cases hω : ω ∈ A
      · simpa [hω] using hs
      · simpa [hω] using htop
    rw [heq]
    exact @MeasurableSet.empty Ω (ℱ r)
