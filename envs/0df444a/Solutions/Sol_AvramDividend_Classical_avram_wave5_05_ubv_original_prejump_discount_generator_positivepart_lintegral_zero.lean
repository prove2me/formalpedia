-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_ubv_original_prejump_discount_generator_positivepart_lintegral_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:42:13.578323+00:00
-- url     : https://prove2.me/submissions/e238d156-577e-4fbf-9b13-0ce860f58799

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_prejump_raw_generator_hjb_allcaps_ae

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

/-!
The predictable generator drift is HJB-nonpositive a.e. on physical-time
clocks, so even its arbitrary extended nonnegative positive part integrates
to zero without demanding global generator integrability at cap contact.
-/

/-- Vanishing positive generator residual along actual pre-event UBV paths. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC0 : C ≠ 0)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ] :
    ∀ᵐ ω ∂P,
      (∫⁻ t : ℝ≥0,
        ENNReal.ofReal
          (if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω then
            X.generator w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) -
            q * w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)
          else 0) ∂μ) = 0 := by
  have hGenerator :=
    avram_wave5_05_ubv_original_prejump_raw_generator_hjb_allcaps_ae
      X hBV q w C hC0 hw_gen x hxc D hD μ
  filter_upwards [hGenerator] with ω hω
  have hZero : ∀ᵐ (t : ℝ≥0) ∂μ,
      ENNReal.ofReal
        (if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω then
          X.generator w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) -
          q * w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)
        else 0) = 0 := by
    filter_upwards [hω] with t ht
    by_cases hPre :
        0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω
    · have hBound := (ht hPre).2
      simpa only [if_pos hPre] using (ENNReal.ofReal_eq_zero.mpr hBound)
    · simp [hPre]
  calc
    (∫⁻ t : ℝ≥0,
      ENNReal.ofReal
        (if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω then
          X.generator w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) -
          q * w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)
        else 0) ∂μ) = ∫⁻ _t : ℝ≥0, (0 : ℝ≥0∞) ∂μ :=
      lintegral_congr_ae hZero
    _ = 0 := by simp
