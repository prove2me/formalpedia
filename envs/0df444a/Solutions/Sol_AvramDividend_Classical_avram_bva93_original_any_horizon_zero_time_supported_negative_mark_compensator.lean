-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva93_original_any_horizon_zero_time_supported_negative_mark_compensator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:21:41.189611+00:00
-- url     : https://prove2.me/submissions/88c1d40d-b911-48de-8285-704e513adac4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bva92_original_mapped_compensator_zero_time_supported_real_integral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : ((ℝ≥0 × Ω) × ℝ) → ℝ) (ω : Ω) (S : ℝ≥0)
    (hSupport : ∀ (t : ℝ≥0), t ≠ 0 → ∀ z : ℝ, H ((t, ω), z) = 0) :
    (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
      ∂(((volume : Measure ℝ).restrict (Icc 0 (S : ℝ))).map Real.toNNReal)) = 0 := by
  apply avram_bva92_original_mapped_compensator_zero_time_supported_real_integral
    S (fun t => ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ))))
  intro t ht
  have hZero : (fun z : ℝ => H ((t, ω), z)) = fun _ => 0 := by
    funext z
    exact hSupport t ht z
  simp only [hZero, integral_zero]
