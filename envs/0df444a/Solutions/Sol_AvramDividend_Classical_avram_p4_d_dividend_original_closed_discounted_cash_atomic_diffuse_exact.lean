-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_closed_discounted_cash_atomic_diffuse_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T22:12:54.020312+00:00
-- url     : https://prove2.me/submissions/65f70c70-4a55-4019-876c-5ac4d367642b

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_pathwise_atomic_diffuse_measure_sum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The entire original discounted dividend Stieltjes cash paid through
the closed horizon equals its atomic rightpayment cash plus its genuinely
atomless (including singular-continuous) cash, exactly in ENNReal. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (σ : Ω → ℝ≥0∞) (τ : Ω → ℝ≥0) (q : ℝ) :
    ∀ ω : Ω,
      (∫⁻ s in paymentTimes (σ ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) =
      (∫⁻ s in paymentTimes (σ ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂
          (dividendMeasure D ω).restrict
            {t : ℝ | 0 < dividendMeasure D ω {t}}) +
      (∫⁻ s in paymentTimes (σ ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂
          (dividendMeasure D ω).restrict
            {t : ℝ | ¬0 < dividendMeasure D ω {t}}) := by
  intro ω
  have hsplit := avram_p4_d_dividend_original_pathwise_atomic_diffuse_measure_sum
    D hD ω
  conv_lhs => rw [← hsplit]
  simp only [Measure.restrict_add, lintegral_add_measure]
