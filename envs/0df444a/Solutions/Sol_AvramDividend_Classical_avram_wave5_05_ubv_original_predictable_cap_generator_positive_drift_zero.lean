-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_cap_generator_positive_drift_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:54:42.579068+00:00
-- url     : https://prove2.me/submissions/0b92a893-534e-41c9-898e-cdc950b5f16d

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_same_source_cap_linear_generator_positive_drift_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_original_prejump_equals_book_reserve_atomless_nnreal_clock

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

/-!
The nonnegative part of the original compensated
cap-linear source generator drift vanishes on the
actual chronological predictable reserve, even when
the original controlled reserve contacts the cap.
-/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hw_gen : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < ENNReal.ofReal c →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal c)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (hStrategy : IsDividendStrategy 𝓕 D)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ] :
    ∀ᵐ ω ∂P,
      (∫⁻ t : ℝ≥0,
        ENNReal.ofReal
          (if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω then
            X.generator
              (fun y => if y ≤ c then w y else w c + (y - c))
              (Function.leftLim
                (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) -
              q * (if Function.leftLim
                    (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ≤ c then
                w (Function.leftLim
                  (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)
              else w c + (Function.leftLim
                (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t - c))
          else 0) ∂μ) = 0 := by
  have hZero :=
    avram_wave5_05_ubv_same_source_cap_linear_generator_positive_drift_zero
      X hBV q w c hc hw_gen x hxc D hD μ
  have hChron :=
    avram_wave5_05_original_prejump_equals_book_reserve_atomless_nnreal_clock
      X x D hStrategy μ
  filter_upwards [hZero, hChron] with ω hωZero hωChron
  calc
    (∫⁻ t : ℝ≥0,
      ENNReal.ofReal
        (if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω then
          X.generator
            (fun y => if y ≤ c then w y else w c + (y - c))
            (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) -
            q * (if Function.leftLim
                  (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ≤ c then
              w (Function.leftLim
                (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)
            else w c + (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t - c))
        else 0) ∂μ) =
      (∫⁻ t : ℝ≥0,
        ENNReal.ofReal
          (if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω then
            X.generator
              (fun y => if y ≤ c then w y else w c + (y - c))
              (riskProcess X x D t ω) -
              q * (if riskProcess X x D t ω ≤ c then
                w (riskProcess X x D t ω)
              else w c + (riskProcess X x D t ω - c))
          else 0) ∂μ) := by
        apply lintegral_congr_ae
        filter_upwards [hωChron] with t htChron
        by_cases htPos : 0 < t
        · rw [htChron htPos]
        · have hNotLive :
            ¬ (0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω) := by
            intro hh
            exact (htPos hh.1)
          simp [hNotLive]
    _ = 0 := hωZero
