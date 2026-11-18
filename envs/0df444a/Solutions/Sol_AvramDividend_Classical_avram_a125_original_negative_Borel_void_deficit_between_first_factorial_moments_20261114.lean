-- Prove2me | solution 1 for AvramDividend.Classical.avram_a125_original_negative_Borel_void_deficit_between_first_factorial_moments_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T16:12:40.065735+00:00
-- url     : https://prove2.me/submissions/18414908-bc69-4fef-8bcd-7b279ca0ccf7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a127_integer_count_nonvoid_probability_first_second_factorial_moment_bounds_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a130_original_negative_Borel_integer_count_first_second_moments_and_void_event_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ)) :
    let rate : ℝ := (t : ℝ) * (X.ν B).toReal
    let void : ℝ :=
      (P {ω : Ω |
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 t ×ˢ B) = 0}).toReal
    rate - rate ^ 2 ≤ 1 - void ∧ 1 - void ≤ rate := by
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨K, hK, hFirstInt, hSecondInt, hMean, hSecond, hVoid⟩ :=
    avram_a130_original_negative_Borel_integer_count_first_second_moments_and_void_event_20261114
      X hFinite t B hB hNeg
  obtain ⟨hLower, hUpper⟩ :=
    avram_a127_integer_count_nonvoid_probability_first_second_factorial_moment_bounds_20261114
      K hK hFirstInt hSecondInt
  dsimp at hMean hSecond hVoid
  rw [hMean, hSecond, hVoid] at hLower
  rw [hMean, hVoid] at hUpper
  refine ⟨?_, hUpper⟩
  convert hLower using 1 <;> ring
