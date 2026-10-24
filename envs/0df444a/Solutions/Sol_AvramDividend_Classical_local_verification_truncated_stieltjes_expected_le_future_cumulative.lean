-- Prove2me | solution 1 for AvramDividend.Classical.local_verification_truncated_stieltjes_expected_le_future_cumulative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:31:57.184531+00:00
-- url     : https://prove2.me/submissions/e04e2f33-843d-4204-8522-1f2360d6fd42

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_discounted_dividendMeasure_Ico_zero_le_dividend_cumulative
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (σ : Ω → ℝ≥0∞)
    (T S : ℝ≥0) (hTS : T < S) :
    (∫⁻ ω, ∫⁻ r in paymentTimes (σ ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω, ENNReal.ofReal (D S ω) ∂P) := by
  have hTSreal : (T : ℝ) < (S : ℝ) := by
    exact_mod_cast hTS
  apply lintegral_mono
  intro ω
  calc
    (∫⁻ r in paymentTimes (σ ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω)) ≤
        (∫⁻ r in Ico (0 : ℝ) (S : ℝ),
          ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω)) := by
      apply lintegral_mono_set
      intro r hr
      exact ⟨hr.1.1, lt_of_le_of_lt hr.2 hTSreal⟩
    _ ≤ ENNReal.ofReal (D S ω) :=
      discounted_dividendMeasure_Ico_zero_le_dividend_cumulative
        D hD ω q hq S
