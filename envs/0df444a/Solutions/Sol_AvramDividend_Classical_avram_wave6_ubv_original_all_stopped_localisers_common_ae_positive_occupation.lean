-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_ubv_original_all_stopped_localisers_common_ae_positive_occupation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T18:04:45.191662+00:00
-- url     : https://prove2.me/submissions/40d6bb25-a1b9-4b4e-9c41-8f2dd5e6d1dd

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.OuterMeasure.AE
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_stopped_sigma_finite_zero_occupation

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
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (σ : ℕ → Ω → ℝ≥0∞)
    (hσ : ∀ n ω, σ n ω ≤ ruinTime X x D ω)
    (times horizons : ℕ → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b →
      ∃ m : ℕ, a < times m ∧ times m < b)
    (hpos : ∀ n : ℕ, 0 < horizons n)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε →
      ∃ n : ℕ, horizons n ≤ ε)
    (μ : Measure ℝ≥0) [SFinite μ] :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      ∀ᵐ (t : ℝ≥0) ∂μ,
        (t : ℝ≥0∞) < σ n ω →
          0 < riskProcess X x D t ω := by
  rw [ae_all_iff]
  intro n
  exact avram_wave5_ubv_original_stopped_sigma_finite_zero_occupation
    X hBV x D hD.1.1 (σ n) (hσ n)
    times horizons hdense hpos hcofinal μ
end
