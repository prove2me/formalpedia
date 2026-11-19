-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_purejump_ubv_joint_high_rate_low_square_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T17:21:01.44941+00:00
-- url     : https://prove2.me/submissions/5b4145e0-ae30-4141-a3b2-bae04e77f3f8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_f6_purejump_ubv_negative_jump_intensity_infinite
import Theorems.Thm_AvramDividend_Classical_negative_jump_real_poisson_rates_tendsto_top
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_source_small_negative_jump_square_intensity_tendsto_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hσ : X.σ = 0)
    (R : ℝ) (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ n : ℕ,
      R ≤ (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal ∧
      (∫⁻ z in Ioo (0 : ℝ) (1 / ((n : ℝ) + 1)),
        ENNReal.ofReal (z ^ 2) ∂(X.ν.map (fun y : ℝ => -y))) < ε := by
  have hMass : X.ν (Iio (0 : ℝ)) = ⊤ :=
    avram_f6_purejump_ubv_negative_jump_intensity_infinite X hBV hσ
  have hRate := negative_jump_real_poisson_rates_tendsto_top
    X.ν X.ν_integrable hMass 1 (by norm_num)
  have hHigh : ∀ᶠ n : ℕ in atTop,
      R ≤ (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal := by
    have h := hRate.eventually (eventually_ge_atTop R)
    simpa only [one_mul] using h
  have hLow := avram_wave4_04_source_small_negative_jump_square_intensity_tendsto_zero X
  have hSmall : ∀ᶠ n : ℕ in atTop,
      (∫⁻ z in Ioo (0 : ℝ) (1 / ((n : ℝ) + 1)),
        ENNReal.ofReal (z ^ 2) ∂(X.ν.map (fun y : ℝ => -y))) < ε :=
    hLow.eventually (eventually_lt_nhds hε)
  obtain ⟨n, hRateN, hSmallN⟩ := (hHigh.and hSmall).exists
  exact ⟨n, hRateN, hSmallN⟩
