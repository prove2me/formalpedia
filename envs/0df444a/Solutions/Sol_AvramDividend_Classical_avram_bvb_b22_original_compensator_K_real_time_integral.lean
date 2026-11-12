-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_b22_original_compensator_K_real_time_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T23:44:31.692224+00:00
-- url     : https://prove2.me/submissions/afe8e376-3005-40b3-b59b-11cffaa9a3a8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Convert the original marked compensator time map to real time on the finite horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ) (ω : Ω) (H : (ℝ≥0 × Ω) × ℝ → ℝ)
    (hMeas : AEStronglyMeasurable
      (fun t : ℝ≥0 => ∫ z,
        H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ))))
      (((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)) :
    (∫ t, ∫ z,
      H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
      ∂(((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)) =
    (∫ t in Icc 0 T, ∫ z,
      H ((Real.toNNReal t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))) := by
  exact integral_map continuous_real_toNNReal.measurable.aemeasurable hMeas
