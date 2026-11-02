-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_ubv_original_stopped_sigma_finite_zero_occupation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:42:06.730347+00:00
-- url     : https://prove2.me/submissions/d25a0d2c-08dd-49c5-88f4-f130b4861099

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonneg_before_ruin
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_same_source_positive_preruin_sigma_finite_occupation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (σ : Ω → ℝ≥0∞)
    (hσ : ∀ ω, σ ω ≤ ruinTime X x D ω)
    (times horizons : ℕ → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b →
      ∃ m : ℕ, a < times m ∧ times m < b)
    (hpos : ∀ n : ℕ, 0 < horizons n)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε →
      ∃ n : ℕ, horizons n ≤ ε)
    (μ : Measure ℝ≥0) [SFinite μ] :
    ∀ᵐ ω ∂P, ∀ᵐ (t : ℝ≥0) ∂μ,
      (t : ℝ≥0∞) < σ ω →
        0 < riskProcess X x D t ω := by
  have hpre : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω →
        0 ≤ riskProcess X x D s ω := by
    intro ω s hs
    exact riskProcess_nonneg_before_ruin X x D ω s hs
  have hocc := avram_wave4_04_ubv_same_source_positive_preruin_sigma_finite_occupation
    X hBV x D hD hpre times horizons hdense hpos hcofinal μ
  filter_upwards [hocc] with ω hω
  filter_upwards [hω] with t ht
  intro hlt
  exact ht (lt_of_lt_of_le hlt (hσ ω))
