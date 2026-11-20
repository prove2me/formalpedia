-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_actual_Levy_negative_mark_JL_integral_cancellation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T07:05:25.952125+00:00
-- url     : https://prove2.me/submissions/5e9641b0-aa20-4b88-8cf7-80bb021ab1da

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_negative_mark_JL_compensator_integral_cancellation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (η : ℝ) (S d : ℝ → ℝ)
    (hη : 0 < η) (hηone : η < 1)
    (hH : Integrable (fun z => S z -
      (if -1 < z then z * d z else 0))
      (X.ν.restrict (Iio (0 : ℝ))))
    (hL : Integrable (fun z => if z ∈ Ioo (-1 : ℝ) (-η) then
      z * d z else 0)
      (X.ν.restrict (Iio (0 : ℝ)))) :
    (∫ z in Iio (0 : ℝ), S z -
      (if -1 < z then z * d z else 0) ∂X.ν) +
    (∫ z in Iio (0 : ℝ),
      (if z ∈ Ioo (-1 : ℝ) (-η) then z * d z else 0) ∂X.ν) =
    (∫ z in Iio (0 : ℝ),
      S z - (if -η ≤ z then z * d z else 0) ∂X.ν) := by
  have hneg : ∀ᵐ z ∂(X.ν.restrict (Iio (0 : ℝ))), z < 0 := by
    exact ae_restrict_mem measurableSet_Iio
  exact
    AvramDividend.Classical.avram_pj_workerC_original_negative_mark_JL_compensator_integral_cancellation
      (X.ν.restrict (Iio (0 : ℝ))) η S d hη hηone hneg hH hL

