-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_original_levy_outer_measure_negative_mark_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:58:56.980436+00:00
-- url     : https://prove2.me/submissions/89cef758-7c4c-417d-a5ab-0b58b3e3fce4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (B : Set ℝ) :
    X.ν B = X.ν (B ∩ Iio (0 : ℝ)) := by
  have hcover : B ⊆ (B ∩ Iio (0 : ℝ)) ∪ Ici (0 : ℝ) := by
    intro y hy
    by_cases h : y < 0
    · exact Or.inl ⟨hy, h⟩
    · exact Or.inr (le_of_not_gt h)
  apply le_antisymm
  · calc
      X.ν B ≤ X.ν ((B ∩ Iio (0 : ℝ)) ∪ Ici (0 : ℝ)) :=
        measure_mono hcover
      _ ≤ X.ν (B ∩ Iio (0 : ℝ)) + X.ν (Ici (0 : ℝ)) :=
        measure_union_le _ _
      _ = X.ν (B ∩ Iio (0 : ℝ)) := by rw [X.ν_Ici, add_zero]
  · exact measure_mono inter_subset_left
