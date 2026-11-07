-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_loc6_topcap_original_stopped_closed_payoff_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T08:42:27.216862+00:00
-- url     : https://prove2.me/submissions/ea37faee-0bb4-48e7-b96d-65ed08c566db

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_infinitecap_candidate_globally_nonnegative

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact original stopped reward is nonnegative, with the closed payment
    interval, right-limit reserve and negative ruin overshoot unchanged. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (D : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hCtop : C = ⊤) :
    ∀ ω, 0 ≤ Term ω + Cash ω := by
  have hw_nonneg : ∀ y : ℝ, 0 ≤ w y :=
    avram_ubv_loc6_infinitecap_candidate_globally_nonnegative
      C hC w hw0 hw_cont hw_neg hw_smooth hw_grad hCtop
  intro ω
  have hT : 0 ≤ Term ω := by
    rw [hTerm ω]
    exact mul_nonneg (le_of_lt (Real.exp_pos _)) (hw_nonneg (W ω))
  have hCashNN : 0 ≤ Cash ω := by
    rw [hCash ω]
    exact ENNReal.toReal_nonneg
  exact add_nonneg hT hCashNN
