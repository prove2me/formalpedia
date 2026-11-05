-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_discounted_stopped_atomic_diffuse_cash_le_total
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T22:20:20.50662+00:00
-- url     : https://prove2.me/submissions/f954c06b-3d74-4e58-97ba-3b6342b3fa34

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_closed_discounted_cash_atomic_diffuse_exact

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Each genuine original stopped atomic and diffuse discounted dividend
Cash component is bounded by the full original discounted Cash, including
both endpoint conventions and singular-continuous mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (σ : Ω → ℝ≥0∞) (τ : Ω → ℝ≥0) (q : ℝ) :
    ∀ ω : Ω,
      (∫⁻ s in paymentTimes (σ ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂
          (dividendMeasure D ω).restrict
            {t : ℝ | 0 < dividendMeasure D ω {t}}) ≤
        (∫⁻ s in paymentTimes (σ ω) ∩ Iic (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ∧
      (∫⁻ s in paymentTimes (σ ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂
          (dividendMeasure D ω).restrict
            {t : ℝ | ¬0 < dividendMeasure D ω {t}}) ≤
        (∫⁻ s in paymentTimes (σ ω) ∩ Iic (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) := by
  intro ω
  have hsplit := avram_p4_d_dividend_original_closed_discounted_cash_atomic_diffuse_exact
    D hD σ τ q ω
  constructor
  · rw [hsplit]
    exact le_add_of_nonneg_right (by positivity)
  · rw [hsplit]
    exact le_add_of_nonneg_left (by positivity)
