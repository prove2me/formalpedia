-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_original_levy_measure_arbitrary_mark_negative_restriction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:43:10.848897+00:00
-- url     : https://prove2.me/submissions/8e68656c-2fae-4cfd-883d-0af3a3106860

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-! The original ν charges only strictly negative marks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (B : Set ℝ) (hB : MeasurableSet B) :
    X.ν B = X.ν (B ∩ Iio (0 : ℝ)) := by
  have hsplit : B = (B ∩ Iio (0 : ℝ)) ∪ (B ∩ Ici (0 : ℝ)) := by
    ext y
    constructor
    · intro hy
      by_cases hneg : y < 0
      · exact Or.inl ⟨hy, hneg⟩
      · exact Or.inr ⟨hy, le_of_not_gt hneg⟩
    · rintro (hy | hy)
      · exact hy.1
      · exact hy.1
  have hdisj : Disjoint (B ∩ Iio (0 : ℝ)) (B ∩ Ici (0 : ℝ)) := by
    apply Set.disjoint_left.mpr
    intro y hy hz
    have hneg : y < (0 : ℝ) := by simpa only [Set.mem_Iio] using hy.2
    have hnonneg : (0 : ℝ) ≤ y := by simpa only [Set.mem_Ici] using hz.2
    exact (not_lt_of_ge hnonneg) hneg
  have hzero : X.ν (B ∩ Ici (0 : ℝ)) = 0 := by
    apply le_antisymm
    · calc
        X.ν (B ∩ Ici (0 : ℝ)) ≤ X.ν (Ici (0 : ℝ)) :=
          measure_mono inter_subset_right
        _ = 0 := X.ν_Ici
    · exact bot_le
  have hmeas : MeasurableSet (B ∩ Ici (0 : ℝ)) :=
    hB.inter isClosed_Ici.measurableSet
  calc
    X.ν B = X.ν ((B ∩ Iio (0 : ℝ)) ∪ (B ∩ Ici (0 : ℝ))) := by rw [← hsplit]
    _ = X.ν (B ∩ Iio (0 : ℝ)) + X.ν (B ∩ Ici (0 : ℝ)) :=
      measure_union hdisj hmeas
    _ = X.ν (B ∩ Iio (0 : ℝ)) := by simp [hzero]
