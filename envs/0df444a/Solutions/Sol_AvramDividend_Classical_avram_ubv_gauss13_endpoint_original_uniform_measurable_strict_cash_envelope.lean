-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gauss13_endpoint_original_uniform_measurable_strict_cash_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T07:29:18.638683+00:00
-- url     : https://prove2.me/submissions/dd61dbc3-962b-45ea-a892-94a62d752e13

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_bounded_random_clock_full_stieltjes_cash_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_endpoint_original_bounded_measurable_strict_cash_L1
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A single integrable original stopped cash envelope controls every
    bounded measurable physical-grid prefix, including non-stopping floors. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (σ : ℕ → Ω → ℝ≥0)
    (hσmeas : ∀ k, Measurable (fun ω : Ω => (σ k ω : ℝ)))
    (hσbound : ∀ k ω, σ k ω ≤ T) :
    Integrable (fun ω => (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal) P ∧
    (∀ k, Integrable (fun ω => (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal) P) ∧
    (∀ k ω, 0 ≤ (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal ∧
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal ≤ (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal) := by
  have hCashT : Integrable (fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal) P := by
    simpa only [] using
      (avram_wave6_08_original_bounded_random_clock_full_stieltjes_cash_integrable
        X x C D hD q (fun _ : Ω => T) T measurable_const
        (by intro ω; exact le_rfl))
  refine ⟨hCashT, ?_, ?_⟩
  · intro k
    exact avram_ubv_gauss13_endpoint_original_bounded_measurable_strict_cash_L1
      X x C D hD q hq (σ k) (hσmeas k) T (hσbound k)
  · intro k ω
    constructor
    · exact ENNReal.toReal_nonneg
    · have hclock : (σ k ω : ℝ) ≤ (T : ℝ) := by
        exact_mod_cast hσbound k ω
      have hle :
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (σ k ω : ℝ),
            ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)) ≤
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
            ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)) := by
        apply lintegral_mono_set
        intro t ht
        exact ⟨ht.1, le_trans (le_of_lt ht.2) hclock⟩
      have hfinite :=
        avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
          D hD.1.1 ω (ruinTime X x D ω) T q hq
      exact ENNReal.toReal_mono (ne_of_lt hfinite) hle
