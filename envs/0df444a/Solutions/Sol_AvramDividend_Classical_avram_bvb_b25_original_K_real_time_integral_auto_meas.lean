-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_b25_original_K_real_time_integral_auto_meas
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T16:15:00.699208+00:00
-- url     : https://prove2.me/submissions/114b23d6-2343-47e3-a901-ae995118e80b

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b23_original_K_exact_real_time_integral
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b23_original_stopped_H_mark_fibre_eq_discounted_rate
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b24_original_K_closed_cap_real_time_rate_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b22_original_prepayment_leftlim_path_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bva21_closed_cap_continuous_kernel_mask_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bva21_original_K_negative_mark_real_time_bridge
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q T : ℝ) (hT : 0 < T)
    (n : ℕ) (ω : Ω)
    (hψ : ContinuousOn
      (fun b : ℝ => ∫ z in Iio (0 : ℝ), w (b + z) - w b ∂X.ν)
      {b : ℝ | 0 ≤ b ∧ ENNReal.ofReal b ≤ C}) :
    let U : ℝ≥0 → Ω → ℝ := fun r η => Function.leftLim
      (fun z : ℝ≥0 => x + X.X z η - rightLimit D z η) r
    let H : (ℝ≥0 × Ω) × ℝ → ℝ := fun p =>
      if 0 < p.1.1 ∧ (p.1.1 : ℝ) < T - T / ((n : ℝ) + 2) ∧
         (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧
         0 ≤ U p.1.1 p.1.2 ∧ ENNReal.ofReal (U p.1.1 p.1.2) ≤ C ∧ p.2 < 0
      then Real.exp (-(q * (p.1.1 : ℝ))) *
        (w (U p.1.1 p.1.2 + p.2) - w (U p.1.1 p.1.2))
      else 0
    (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
      ∂(((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)) =
    (∫ t in Icc 0 T,
      if 0 < Real.toNNReal t ∧
         ((Real.toNNReal t : ℝ≥0) : ℝ) < T - T / ((n : ℝ) + 2) ∧
         ((Real.toNNReal t : ℝ≥0) : ℝ≥0∞) ≤ ruinTime X x D ω ∧
         0 ≤ U (Real.toNNReal t) ω ∧
         ENNReal.ofReal (U (Real.toNNReal t) ω) ≤ C
      then Real.exp (-(q * ((Real.toNNReal t : ℝ≥0) : ℝ))) *
         ∫ z in Iio (0 : ℝ), w (U (Real.toNNReal t) ω + z) -
                                   w (U (Real.toNNReal t) ω) ∂X.ν
      else 0) := by
  apply avram_bvb_b23_original_K_exact_real_time_integral
  have hK := avram_bvb_b24_original_K_closed_cap_real_time_rate_measurable
    X x C D hD ω q T hT n
    (fun b : ℝ => ∫ z in Iio (0 : ℝ), w (b + z) - w b ∂X.ν) hψ
  convert hK.aestronglyMeasurable using 1
  ext t
  simpa only [and_assoc] using
    (avram_bvb_b23_original_stopped_H_mark_fibre_eq_discounted_rate
      X x C D w q T n ω t)
