-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_weight_uniform_generator_positive_drift_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T14:55:07.429575+00:00
-- url     : https://prove2.me/submissions/1098ee50-5533-4156-844c-9836b2ed27b2

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_cap_generator_and_secant_admissible_only

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

/-!
One original-process conull event annihilates every
weighted positive compensated generator drift at the
genuine predictable reserve. The weight may be infinite,
path-dependent and selected after the conull event.
-/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c})
    (hw_gen : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < ENNReal.ofReal c →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < ENNReal.ofReal c → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal c)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ] :
    ∀ᵐ ω ∂P, ∀ (weight : ℝ≥0 → Ω → ℝ≥0∞),
      (∫⁻ t : ℝ≥0, weight t ω * ENNReal.ofReal
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
  have hGen :=
    (avram_wave5_05_ubv_original_predictable_cap_generator_and_secant_admissible_only
      X hBV q w c hc hw_cont hw_smooth hw_gen hw_grad
      x hxc D hD μ).2
  filter_upwards [hGen] with ω hωGen
  intro weight
  have hZero : ∀ᵐ t : ℝ≥0 ∂μ,
      weight t ω * ENNReal.ofReal
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
          else 0) = 0 := by
    filter_upwards [hωGen] with t htGen
    by_cases hLive :
        0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω
    · have hBound := (htGen hLive).2
      have hOfReal :
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
          else 0) = 0 := by
        simpa only [if_pos hLive] using
          (ENNReal.ofReal_eq_zero.mpr hBound)
      rw [hOfReal]
      simp
    · simp [hLive]
  calc
    (∫⁻ t : ℝ≥0, weight t ω * ENNReal.ofReal
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
        (∫⁻ _ : ℝ≥0, (0 : ℝ≥0∞) ∂μ) :=
      lintegral_congr_ae hZero
    _ = 0 := by simp
