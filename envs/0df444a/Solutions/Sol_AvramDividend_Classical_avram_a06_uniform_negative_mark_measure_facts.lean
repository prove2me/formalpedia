-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_uniform_negative_mark_measure_facts
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T16:52:29.528257+00:00
-- url     : https://prove2.me/submissions/a1e269ec-b56c-48b0-a330-adf3dac9b0e4

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- The compact uniform negative-jump mark law has finite, nonzero diffuse
mass, and assigns no mass to nonnegative jumps. -/
theorem solution :
    ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) (Ici (0 : ℝ)) = 0 ∧
    ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) Set.univ = 1 ∧
    ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) (Iio (0 : ℝ)) < ⊤ ∧
    ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) ≠ 0 ∧
    ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) ≪ volume := by
  let ν : Measure ℝ := (volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)
  have hmass : ν Set.univ = 1 := by
    simp [ν, Measure.restrict_apply_univ, Real.volume_Ioo]
  have hnonnegative : ν (Ici (0 : ℝ)) = 0 := by
    change ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) (Ici 0) = 0
    rw [Measure.restrict_apply measurableSet_Ici]
    have hs : Ici (0 : ℝ) ∩ Ioo (-1 : ℝ) 0 = ∅ := by
      ext y
      simp only [mem_inter_iff, mem_Ici, mem_Ioo, mem_empty_iff_false, iff_false]
      intro hy
      exact (not_lt_of_ge hy.1) hy.2.2
    simp [hs]
  have hfinite : ν (Iio (0 : ℝ)) < ⊤ := by
    calc
      ν (Iio 0) ≤ ν Set.univ := measure_mono (subset_univ _)
      _ = 1 := hmass
      _ < ⊤ := ENNReal.one_lt_top
  have hnonzero : ν ≠ 0 := by
    intro h
    rw [h] at hmass
    simp at hmass
  have hdiffuse : ν ≪ (volume : Measure ℝ) := by
    have hle : ν ≤ (volume : Measure ℝ) := Measure.restrict_le_self
    exact Measure.absolutelyContinuous_of_le hle
  exact ⟨hnonnegative, hmass, hfinite, hnonzero, hdiffuse⟩
