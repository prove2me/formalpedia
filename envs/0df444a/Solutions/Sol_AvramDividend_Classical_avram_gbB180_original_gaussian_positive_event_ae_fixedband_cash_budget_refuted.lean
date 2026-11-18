-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB180_original_gaussian_positive_event_ae_fixedband_cash_budget_refuted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T19:07:56.892379+00:00
-- url     : https://prove2.me/submissions/f182ddff-6f46-4802-bae8-222ff9cdc274

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB155_original_centered_gaussian_tube_stopped_cash_conditional_strict_excess
import Theorems.Thm_AvramDividend_Classical_avram_gbB156_centered_short_Brownian_tube_implies_original_source_tube
import Theorems.Thm_AvramDividend_Classical_avram_gbB163_original_equal_cap_barrier_finite_discounted_strict_stopped_cash
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section
/-- Positive event and bounded original Gaussian noise exclude fixed-band cash budgets. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (E : Set Ω) (hE : MeasurableSet E) (hPositive : 0 < P E)
    (B : Ω → ℝ≥0 → ℝ)
    (hSource : ∀ ω ∈ E, ∀ s : ℝ≥0, s ≤ (1 / 1000 : ℝ≥0) →
      X.X s ω = B ω s + 2 * (s : ℝ))
    (hCentered : ∀ ω ∈ E, ∀ s : ℝ≥0, s ≤ (1 / 1000 : ℝ≥0) →
      |B ω s| ≤ (1 / 4000 : ℝ))
    (N : Ω → ℝ)
    (hNoise : ∀ᵐ ω ∂(P.restrict E), |N ω| ≤ (1 / 4000 : ℝ))
    (hBudget : ∀ᵐ ω ∂(P.restrict E), Real.exp (-(1 / 100000 : ℝ)) *
        (2 * (riskProcess X (1 / 8 : ℝ) (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) (1 / 1000 : ℝ≥0) ω) - 4 * (riskProcess X (1 / 8 : ℝ) (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) (1 / 1000 : ℝ≥0) ω) ^ 2) +
      (∫⁻ t in paymentTimes
      (ruinTime X (1 / 8 : ℝ) (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω) ∩ Iio ((1 / 1000 : ℝ≥0) : ℝ),
      ENNReal.ofReal (Real.exp (-((1 / 100 : ℝ) * t)))
        ∂(dividendMeasure (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω)).toReal - (3 / 16 : ℝ) ≤ N ω + (1 / 1936 : ℝ)) :
    False := by
  haveI : NeZero (P E) := ⟨ne_of_gt hPositive⟩
  haveI : NeZero (P.restrict E) := inferInstance
  have hMem := ae_restrict_mem (μ := P) hE
  obtain ⟨ω, hωE, hNω, hBudgetω⟩ :=
    (hMem.and (hNoise.and hBudget)).exists
  have hTube :=
    avram_gbB156_centered_short_Brownian_tube_implies_original_source_tube
      X ω (B ω) (hSource ω hωE) (hCentered ω hωE)
  have hFinite :=
    avram_gbB163_original_equal_cap_barrier_finite_discounted_strict_stopped_cash
      X ω (1 / 1000 : ℝ≥0) (1 / 100 : ℝ) (by norm_num)
  have hContra :=
    avram_gbB155_original_centered_gaussian_tube_stopped_cash_conditional_strict_excess
      X ω (B ω) (hSource ω hωE) (hCentered ω hωE)
      hTube hFinite (N ω) hNω
  exact hContra hBudgetω
