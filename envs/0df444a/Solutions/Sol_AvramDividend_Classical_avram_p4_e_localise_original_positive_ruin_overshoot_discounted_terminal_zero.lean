-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_positive_ruin_overshoot_discounted_terminal_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:41:20.752874+00:00
-- url     : https://prove2.me/submissions/ef1dca6f-2688-4526-b29e-fbb1a7f60bab

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- At genuine strictly positive ruin, a negative prepayment reserve gives zero discounted terminal extension. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (τ : Ω → ℝ≥0) (W : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (w : ℝ → ℝ) (hwneg : ∀ y : ℝ, y < 0 → w y = 0)
    (ω : Ω) (hτpos : 0 < τ ω)
    (hruin : ruinTime X x D ω ≤ (τ ω : ℝ≥0∞))
    (hOvershoot : riskProcess X x D (τ ω) ω < 0) :
    Real.exp (-(q * (τ ω : ℝ))) * w (W ω) = 0 := by
  have hbranch : ¬ (τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω) := by
    push_neg
    exact ⟨ne_of_gt hτpos, hruin⟩
  rw [hW ω, if_neg hbranch, hwneg _ hOvershoot, mul_zero]
