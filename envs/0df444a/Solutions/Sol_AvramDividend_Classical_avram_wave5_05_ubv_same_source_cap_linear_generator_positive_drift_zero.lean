-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_ubv_same_source_cap_linear_generator_positive_drift_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:48:41.1762+00:00
-- url     : https://prove2.me/submissions/f710c73d-4468-4e81-b9b1-242c0bb3e8f1

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_allcap_actual_generator_interior_no_grid
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_cap_linear_extension_source_generator_eq_interior

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Physical-time positive generator drift vanishes for the original capped
controlled UBV source, including all positive-time cap contacts. -/
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
    (μ : Measure ℝ≥0) [SFinite μ] :
    ∀ᵐ ω ∂P,
      (∫⁻ t : ℝ≥0,
        ENNReal.ofReal
          (if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω then
            X.generator
              (fun y => if y ≤ c then w y else w c + (y - c))
              (riskProcess X x D t ω) -
              q * (if riskProcess X x D t ω ≤ c then
                w (riskProcess X x D t ω)
              else w c + (riskProcess X x D t ω - c))
          else 0) ∂μ) = 0 := by
  have hC0 : ENNReal.ofReal c ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hc)
  have hInside :=
    avram_wave4_04_ubv_allcap_actual_generator_interior_no_grid
      X hBV x (ENNReal.ofReal c) hC0 D hD hxc μ
  filter_upwards [hInside] with ω hω
  have hZero : ∀ᵐ (t : ℝ≥0) ∂μ,
      ENNReal.ofReal
        (if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω then
          X.generator
            (fun y => if y ≤ c then w y else w c + (y - c))
            (riskProcess X x D t ω) -
            q * (if riskProcess X x D t ω ≤ c then
              w (riskProcess X x D t ω)
            else w c + (riskProcess X x D t ω - c))
        else 0) = 0 := by
    filter_upwards [hω] with t ht
    by_cases hPre :
        0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω
    · obtain ⟨hPos, hCap⟩ := ht hPre
      let u : ℝ := riskProcess X x D t ω
      have hu : 0 < u := hPos
      have hucE : ENNReal.ofReal u < ENNReal.ofReal c := hCap
      have huc : u < c :=
        (ENNReal.ofReal_lt_ofReal_iff hc).mp hucE
      have hHJB := (hw_gen u hu hucE).2
      have hGenEq :=
        avram_wave4_04_cap_linear_extension_source_generator_eq_interior
          X w c u huc
      have hVal : (if u ≤ c then w u else w c + (u - c)) = w u :=
        if_pos (le_of_lt huc)
      have hBound :
          X.generator
            (fun y => if y ≤ c then w y else w c + (y - c)) u -
            q * (if u ≤ c then w u else w c + (u - c)) ≤ 0 := by
        rw [hGenEq, hVal]
        exact hHJB
      have hSource :
          X.generator
            (fun y => if y ≤ c then w y else w c + (y - c))
            (riskProcess X x D t ω) -
            q * (if riskProcess X x D t ω ≤ c then
              w (riskProcess X x D t ω)
            else w c + (riskProcess X x D t ω - c)) ≤ 0 := hBound
      simpa only [if_pos hPre] using
        (ENNReal.ofReal_eq_zero.mpr hSource)
    · simp [hPre]
  calc
    (∫⁻ t : ℝ≥0,
      ENNReal.ofReal
        (if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω then
          X.generator
            (fun y => if y ≤ c then w y else w c + (y - c))
            (riskProcess X x D t ω) -
            q * (if riskProcess X x D t ω ≤ c then
              w (riskProcess X x D t ω)
            else w c + (riskProcess X x D t ω - c))
        else 0) ∂μ) = ∫⁻ _ : ℝ≥0, (0 : ℝ≥0∞) ∂μ :=
      lintegral_congr_ae hZero
    _ = 0 := by simp
