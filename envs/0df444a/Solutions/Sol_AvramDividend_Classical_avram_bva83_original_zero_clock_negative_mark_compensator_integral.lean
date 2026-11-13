-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva83_original_zero_clock_negative_mark_compensator_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T21:29:06.705257+00:00
-- url     : https://prove2.me/submissions/b052cab4-8497-4aa9-ab2d-1ec9615c33e4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bva82_original_zero_horizon_compensator_clock_and_real_integrals
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
    (H : ((ℝ≥0 × Ω) × ℝ) → ℝ) (ω : Ω) :
    (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
      ∂(((volume : Measure ℝ).restrict (Icc 0 (0 : ℝ))).map Real.toNNReal)) = 0 := by
  exact
    (avram_bva82_original_zero_horizon_compensator_clock_and_real_integrals).2
      (fun t => ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ))))
