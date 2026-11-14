-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_capHJB38_original_BV_boundary_unmasked_sign_of_dominated_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:47:29.794832+00:00
-- url     : https://prove2.me/submissions/2fd3bed7-b275-4e1b-b2dd-b23a22eb2386

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bva_capHJB35_original_BV_finitecap_unmasked_generator_sign_of_jump_limit
import Theorems.Thm_AvramDividend_Classical_avram_bva_capHJB36_original_full_negative_mark_rate_DCT
import Theorems.Thm_AvramDividend_Classical_avram_bva_capHJB37_original_shifted_candidate_ae_continuous
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hwc : ContinuousAt w C.toReal)
    (hAway : ∀ r : ℝ, r ≠ 0 → ContinuousAt w r)
    (hwGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (y : ℕ → ℝ)
    (hy : Tendsto y atTop (𝓝 C.toReal))
    (hyInside : ∀ n, 0 < y n ∧ ENNReal.ofReal (y n) < C)
    (g : ℝ → ℝ) (hg : Integrable g (X.ν.restrict (Iio (0 : ℝ))))
    (hMeas : ∀ n, AEStronglyMeasurable
      (fun z : ℝ => w (y n + z) - w (y n))
      (X.ν.restrict (Iio (0 : ℝ))))
    (hDom : ∀ n, ∀ᵐ z ∂(X.ν.restrict (Iio (0 : ℝ))),
      ‖w (y n + z) - w (y n)‖ ≤ ‖g z‖) :
    X.drift + (∫ z in Iio (0 : ℝ),
      w (C.toReal + z) - w C.toReal ∂X.ν)
      - q * w C.toReal ≤ 0 := by
  have hAe : ∀ᵐ z ∂(X.ν.restrict (Iio (0 : ℝ))),
      ContinuousAt w (C.toReal + z) :=
    avram_bva_capHJB37_original_shifted_candidate_ae_continuous
      X hStanding hBV w hAway C.toReal
  have hMark : Tendsto (fun n => ∫ z in Iio (0 : ℝ),
      w (y n + z) - w (y n) ∂X.ν) atTop
      (𝓝 (∫ z in Iio (0 : ℝ),
      w (C.toReal + z) - w C.toReal ∂X.ν)) :=
    avram_bva_capHJB36_original_full_negative_mark_rate_DCT
      X w C.toReal y hy hwc hAe g hg hMeas hDom
  exact avram_bva_capHJB35_original_BV_finitecap_unmasked_generator_sign_of_jump_limit
    X hStanding hBV q w C hC hFinite hwGen hwGrad
    y hyInside (hwc.tendsto.comp hy) hMark
