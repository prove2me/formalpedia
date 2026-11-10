-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_excess18_original_zero_contact_nojump_cash_le_HJB_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T19:45:49.508437+00:00
-- url     : https://prove2.me/submissions/7f962d05-9530-40d9-943f-6c05e4fde867

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_correct12_finite_activity_origin_HJB_drift_ceiling
import Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_postzero_restart_nofuturejump_cash_le_drift

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (a b : ℝ≥0) (hab : a ≤ b)
    (hzeroa : riskProcess X x D a ω -
      (rightLimit D a ω - D a ω) = 0)
    (hpositiveb : 0 ≤ riskProcess X x D b ω -
      (rightLimit D b ω - D b ω))
    (hline : X.X b ω - X.X a ω =
      X.drift * ((b : ℝ) - (a : ℝ))) :
    dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) ≤
      ENNReal.ofReal
        (((q + (X.ν (Iio (0 : ℝ))).toReal) * w 0) *
          ((b : ℝ) - (a : ℝ))) := by
  have hCash :=
    avram_bv_zero13_original_postzero_restart_nofuturejump_cash_le_drift
      X hBV hFinite x C D hD ω a b hab hzeroa hpositiveb hline
  have hDrift :=
    avram_bv_correct12_finite_activity_origin_HJB_drift_ceiling
      X hX hBV hFinite q w C hC hw_cont hw0 hw_neg
      hw_smooth hw_gen hw_grad
  have hDelta : 0 ≤ (b : ℝ) - (a : ℝ) := by
    exact sub_nonneg.mpr (by exact_mod_cast hab)
  calc
    dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) ≤
        ENNReal.ofReal (X.drift * ((b : ℝ) - (a : ℝ))) := hCash
    _ ≤ ENNReal.ofReal
        (((q + (X.ν (Iio (0 : ℝ))).toReal) * w 0) *
          ((b : ℝ) - (a : ℝ))) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hDrift hDelta)
