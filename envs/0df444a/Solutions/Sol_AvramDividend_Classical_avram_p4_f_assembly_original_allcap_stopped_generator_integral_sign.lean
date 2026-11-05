-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_allcap_stopped_generator_integral_sign
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T15:32:05.216647+00:00
-- url     : https://prove2.me/submissions/f8db7c0e-abb5-41d2-a193-dcc0d5b28899

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_allcap_predictable_stopped_generator_HJB_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (hC0 : C ≠ 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C)
    (τ : Ω → ℝ≥0∞) (hτ : ∀ ω, τ ω ≤ ruinTime X x D ω)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ]
    (w : ℝ → ℝ) (q : ℝ)
    (hwGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (G : Ω → ℝ)
    (hG : ∀ ω, G ω =
      ∫ t : ℝ≥0, if 0 < t ∧ (t : ℝ≥0∞) < τ ω then
        Real.exp (-(q * (t : ℝ))) *
          (X.generator w (Function.leftLim
             (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) -
           q * w (Function.leftLim
             (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t))
      else 0 ∂μ)
    (hGI : Integrable G P) :
    Integrable G P ∧ ∀ᵐ ω ∂P, G ω ≤ 0 := by
  refine ⟨hGI, ?_⟩
  filter_upwards [
    avram_p4_e_localise_original_allcap_predictable_stopped_generator_HJB_ae
      X hBV x C hC0 D hD hxc τ hτ μ w q hwGen
  ] with ω hω
  rw [hG ω]
  apply MeasureTheory.integral_nonpos_of_ae
  filter_upwards [hω] with t ht
  split_ifs with htime
  · exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Real.exp_pos _))
      (ht htime.1 htime.2).2
  · exact le_refl 0
