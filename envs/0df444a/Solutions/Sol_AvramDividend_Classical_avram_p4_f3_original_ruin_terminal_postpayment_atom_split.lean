-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_ruin_terminal_postpayment_atom_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:51:42.864501+00:00
-- url     : https://prove2.me/submissions/1b736a0b-e5f5-486c-abfd-128324465000

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The genuine ruin branch retains the exact missing right-payment atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (τ : Ω → ℝ≥0) (W : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (ω : Ω) :
    W ω =
      (riskProcess X x D (τ ω) ω -
        (rightLimit D (τ ω) ω - D (τ ω) ω)) +
      (if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        (0 : ℝ) else rightLimit D (τ ω) ω - D (τ ω) ω) := by
  by_cases h : τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
  · rw [hW ω, if_pos h, if_pos h]
    change x + X.X (τ ω) ω - rightLimit D (τ ω) ω =
      (x + X.X (τ ω) ω - D (τ ω) ω -
        (rightLimit D (τ ω) ω - D (τ ω) ω)) + 0
    ring
  · rw [hW ω, if_neg h, if_neg h]
    change x + X.X (τ ω) ω - D (τ ω) ω =
      (x + X.X (τ ω) ω - D (τ ω) ω -
        (rightLimit D (τ ω) ω - D (τ ω) ω)) +
          (rightLimit D (τ ω) ω - D (τ ω) ω)
    ring
