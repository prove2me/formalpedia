-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_any_clock_paid_reward_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:32:36.05669+00:00
-- url     : https://prove2.me/submissions/2b3cb3b0-8ad5-4760-aef2-33327e63e981

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_exact_stopped_W_Term_nonnegative_all_branches
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
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hwCont : ContinuousOn w (Ici 0))
    (hwNeg : ∀ y < 0, w y = 0)
    (hwSmooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (σ : Ω → ℝ≥0) :
    ∀ ω, 0 ≤
      Real.exp (-(q * (σ ω : ℝ))) *
        w (if σ ω = 0 ∨ (σ ω : ℝ≥0∞) < ruinTime X x D ω then
          x + X.X (σ ω) ω - rightLimit D (σ ω) ω
          else riskProcess X x D (σ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal := by
  let W : Ω → ℝ := fun η =>
    if σ η = 0 ∨ (σ η : ℝ≥0∞) < ruinTime X x D η then
      x + X.X (σ η) η - rightLimit D (σ η) η
    else riskProcess X x D (σ η) η
  let Term : Ω → ℝ := fun η =>
    Real.exp (-(q * (σ η : ℝ))) * w (W η)
  have hTerm : ∀ η, 0 ≤ Term η :=
    avram_p4_e_localise_original_exact_stopped_W_Term_nonnegative_all_branches
      X hBV w C hC hw0 hwCont hwNeg hwSmooth hwGrad x hxc
      D hD q σ W Term
      (by intro η; rfl) (by intro η; rfl)
  intro ω
  have hCash : 0 ≤
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal := by
    positivity
  simpa [Term, W] using add_nonneg (hTerm ω) hCash
