-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_past_event_future_negative_Borel_void_exact_exponential_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T17:40:55.1315+00:00
-- url     : https://prove2.me/submissions/4ebaf36d-efd1-42e0-b98c-7f81da23161e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_future_mark_void_event_probability_factor
import Theorems.Thm_AvramDividend_Classical_avram_a25_original_shifted_negative_Borel_physical_void_exact_20261115
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Actual original future negative-mark void probability factors from each past event with its exact exponent. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (s T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ))
    (A : Set Ω) (hApast : MeasurableSet[𝓕 s] A)
    (hAraw : MeasurableSet A) :
    (P (A ∩ {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ B) = 0})).toReal =
      (P A).toReal * Real.exp (-((T : ℝ) * (X.ν B).toReal)) := by
  have hFactor :=
    avram_wave7_06_original_intrinsic_future_mark_void_event_probability_factor
      X s (s + T) (by exact le_add_of_nonneg_right (bot_le))
      B hB A hApast hAraw
  have hVoid :=
    avram_a25_original_shifted_negative_Borel_physical_void_exact_20261115
      X hFinite s T B hB hNeg
  rw [hFactor, ENNReal.toReal_mul]
  exact congrArg ((P A).toReal * ·) hVoid
