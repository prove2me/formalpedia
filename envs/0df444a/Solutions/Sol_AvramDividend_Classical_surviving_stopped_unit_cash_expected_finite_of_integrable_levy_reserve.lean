-- Prove2me | solution 1 for AvramDividend.Classical.surviving_stopped_unit_cash_expected_finite_of_integrable_levy_reserve
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T22:21:48.735093+00:00
-- url     : https://prove2.me/submissions/92d1eeba-9812-4df4-adf5-c918d8d147e4

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_surviving_stopped_dividend_expected_finite_of_integrable_levy_reserve
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Each localised surviving cash interval is dominated by the integrable
    complete discounted Stieltjes reward before the deterministic survival time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (σ : Ω → ℝ≥0∞)
    (T S : ℝ≥0) (hTS : T < S)
    (hXI : Integrable (fun ω => x + X.X S ω) P)
    (k : ℕ) :
    (∫⁻ ω, if (S : ℝ≥0∞) < ruinTime X x D ω then
      (∫⁻ r in
        (paymentTimes (σ ω) ∩ Iic (T : ℝ)) ∩
          Ico (k : ℝ) ((k : ℝ) + 1),
        ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω))
      else 0 ∂P) ≠ ⊤ := by
  have hFull :=
    surviving_stopped_dividend_expected_finite_of_integrable_levy_reserve
      X x D hD q hq σ T S hTS hXI
  have hMon :
      (∫⁻ ω, if (S : ℝ≥0∞) < ruinTime X x D ω then
        (∫⁻ r in
          (paymentTimes (σ ω) ∩ Iic (T : ℝ)) ∩
            Ico (k : ℝ) ((k : ℝ) + 1),
          ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω))
        else 0 ∂P) ≤
      (∫⁻ ω, if (S : ℝ≥0∞) < ruinTime X x D ω then
        (∫⁻ r in paymentTimes (σ ω) ∩ Iic (T : ℝ),
          ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω))
        else 0 ∂P) := by
    apply lintegral_mono
    intro ω
    by_cases hs : (S : ℝ≥0∞) < ruinTime X x D ω
    · have hBlock :
          (∫⁻ r in
            (paymentTimes (σ ω) ∩ Iic (T : ℝ)) ∩
              Ico (k : ℝ) ((k : ℝ) + 1),
            ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω)) ≤
          (∫⁻ r in paymentTimes (σ ω) ∩ Iic (T : ℝ),
            ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω)) :=
        lintegral_mono_set Set.inter_subset_left
      simpa only [if_pos hs] using hBlock
    · simp [hs]
  exact (lt_of_le_of_lt hMon (lt_top_iff_ne_top.mpr hFull)).ne
