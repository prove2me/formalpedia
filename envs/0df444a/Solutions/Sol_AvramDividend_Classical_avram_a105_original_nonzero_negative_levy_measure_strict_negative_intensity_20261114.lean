-- Prove2me | solution 1 for AvramDividend.Classical.avram_a105_original_nonzero_negative_levy_measure_strict_negative_intensity_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:54:32.006234+00:00
-- url     : https://prove2.me/submissions/005fbcce-4459-4f6d-9323-b650f74c3e5c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hNu : X.ν ≠ 0) :
    0 < X.ν (Iio (0 : ℝ)) := by
  by_contra h
  have hZero : X.ν (Iio (0 : ℝ)) = 0 :=
    le_zero_iff.mp (le_of_not_gt h)
  have hCover : (Iio (0 : ℝ) ∪ Ici (0 : ℝ)) = Set.univ := by
    exact Iio_union_Ici
  have hUniv : X.ν Set.univ ≤
      X.ν (Iio (0 : ℝ)) + X.ν (Ici (0 : ℝ)) := by
    rw [← hCover]
    exact measure_union_le _ _
  have hUniv0 : X.ν Set.univ = 0 := by
    apply le_zero_iff.mp
    calc
      X.ν Set.univ ≤ X.ν (Iio (0 : ℝ)) +
          X.ν (Ici (0 : ℝ)) := hUniv
      _ = 0 := by simp [hZero, X.ν_Ici]
  have hZeroEvery (s : Set ℝ) : X.ν s = 0 := by
    exact le_zero_iff.mp
      ((measure_mono (subset_univ s)).trans_eq hUniv0)
  have hMeasureZero : X.ν = 0 := by
    ext s hs
    exact hZeroEvery s
  exact hNu hMeasureZero
