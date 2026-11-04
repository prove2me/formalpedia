-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_atomless_predictable_finite_cap_generator_HJB_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:37:46.197475+00:00
-- url     : https://prove2.me/submissions/666b602e-7780-4cdb-a653-bed33f124332

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_allcap_original_stopped_full_zero_included_no_grid
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_same_source_sigma_finite_cap_occupation
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_original_prejump_equals_book_reserve_atomless_nnreal_clock
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- On an atomless source clock the genuine predictable pre-event reserve obeys interior HJB. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (hDiv : IsDividendStrategy 𝓕 D)
    (hCap : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω → riskProcess X x D s ω ≤ c)
    (τ : Ω → ℝ≥0∞)
    (hτ : ∀ ω, τ ω ≤ ruinTime X x D ω)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ]
    (w : ℝ → ℝ) (q : ℝ)
    (hwGen : ∀ y : ℝ, 0 < y → y < c →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) :
    ∀ᵐ ω ∂P, ∀ᵐ t : ℝ≥0 ∂μ,
      0 < t → (t : ℝ≥0∞) < τ ω →
      X.GeneratorIntegrable w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ∧
        X.generator w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) - q * w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ≤ 0 := by
  have hZero :=
    avram_wave5_ubv_allcap_original_stopped_full_zero_included_no_grid
      X hBV x (ENNReal.ofReal c) D hD τ hτ μ
  have hUpper :=
    avram_wave4_04_ubv_same_source_sigma_finite_cap_occupation
      X hBV x c D hDiv μ hCap
  have hChron :=
    avram_wave5_05_original_prejump_equals_book_reserve_atomless_nnreal_clock
      X x D hDiv μ
  filter_upwards [hZero, hUpper, hChron] with ω hZeroω hUpperω hChronω
  filter_upwards [hZeroω, hUpperω, hChronω] with t ht0 htc hchron
  intro ht hBefore
  have hBeforeRuin : (t : ℝ≥0∞) < ruinTime X x D ω :=
    lt_of_lt_of_le hBefore (hτ ω)
  rw [hchron ht]
  exact hwGen _ (ht0 hBefore) (htc ⟨ht, hBeforeRuin⟩)
